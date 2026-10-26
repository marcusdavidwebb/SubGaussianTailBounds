import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 840. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0840
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5463646687, 5279861183, 5104134601, 4936015060, 4775082341, 4620945124, 4473238522, 4331621878, 4195776780, 4065405287, 3940228320, 3819984213, 3704427397, 3593327203, 3486466778, 3383642093, 3284661033, 3189342572, 3097516013, 3009020285, 2923703307, 2841421389, 2762038695, 2685426733, 2611463890, 2540035003, 2471030956, 2404348312, 2339888968, 2277559831, 2217272524, 2158943107, 2102491818, 2047842830, 1994924029, 1943666799, 1894005826, 1845878918, 1799226825, 1753993082, 1710123855, 1667567800, 1626275929, 1586201484, 1547299817, 1509528285, 1472846138, 1437214425, 1402595904, 1368954947, 1336257466, 1304470830, 1273563797, 1243506437, 1214270078, 1185827233, 1158151550, 1131217755, 1105001599, 1079479808, 1054630039, 1030430838, 1006861590, 983902489, 961534497, 939739305, 918499306, 897797558, 877617759, 857944211, 838761801, 820055968, 801812685, 784018431, 766660170, 749725331, 733201790, 717077844, 701342203, 685983962, 670992594, 656357929, 642070141, 628119734, 614497527, 601194645, 588202501, 575512789, 563117472, 551008771, 539179155, 527621329, 516328229, 505293011, 494509043, 483969897, 473669340, 463601329, 453760003, 444139675, 434734829, 425540109, 416550318, 407760409, 399165482, 390760778, 382541671, 374503670, 366642408, 358953640, 351433243, 344077202, 336881618, 329842695, 322956742, 316220167, 309629474, 303181262, 296872218, 290699119, 284658824]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 840).prefactor = (5001031888277709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 840).cutoff/(generalMeanRows 840).c)).2 =
    (7239631046073/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 840).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 840).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 840).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 840

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 840).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 840).criticalRate j.val*(generalMeanRows 840).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 840).c*(generalMeanRows 840).criticalPoint j.val)).2-
      (generalMeanRows 840).J/2-(generalMeanRows 840).error (generalMeanGrid j.val)+
      (generalMeanRows 840).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 840).c)).2-
      (generalMeanRows 840).J/2-(generalMeanRows 840).error 4 := by
  have he : (generalMeanRows 840).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 840) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 840)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0840

/-! Kernel-checked entropy margins for general spectral rectangle 841. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0841
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5213963739, 5044649764, 4882752841, 4727850491, 4579550192, 4437486755, 4301319995, 4170732631, 4045428415, 3925130439, 3809579611, 3698533276, 3591763965, 3489058260, 3390215756, 3295048123, 3203378243, 3115039416, 3029874645, 2947735963, 2868483828, 2791986562, 2718119824, 2646766142, 2577814462, 2511159744, 2446702578, 2384348837, 2324009346, 2265599583, 2209039392, 2154252726, 2101167397, 2049714851, 1999829954, 1951450797, 1904518502, 1858977059, 1814773157, 1771856032, 1730177328, 1689690963, 1650353002, 1612121540, 1574956595, 1538820000, 1503675309, 1469487706, 1436223916, 1403852128, 1372341917, 1341664172, 1311791030, 1282695809, 1254352955, 1226737978, 1199827403, 1173598718, 1148030329, 1123101512, 1098792371, 1075083801, 1051957445, 1029395665, 1007381501, 985898646, 964931407, 944464687, 924483948, 904975191, 885924929, 867320167, 849148375, 831397473, 814055806, 797112129, 780555587, 764375699, 748562343, 733105738, 717996433, 703225290, 688783472, 674662433, 660853902, 647349874, 634142600, 621224576, 608588532, 596227424, 584134424, 572302916, 560726481, 549398893, 538314115, 527466285, 516849714, 506458879, 496288416, 486333115, 476587914, 467047893, 457708272, 448564402, 439611763, 430845957, 422262709, 413857857, 405627351, 397567250, 389673715, 381943011, 374371497, 366955630, 359691955, 352577108, 345607809, 338780862, 332093150, 325541637, 319123358]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 841).prefactor = (4707031035630941/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 841).cutoff/(generalMeanRows 841).c)).2 =
    (399882316673811/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 841).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 841).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 841).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 841

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 841).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 841).criticalRate j.val*(generalMeanRows 841).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 841).c*(generalMeanRows 841).criticalPoint j.val)).2-
      (generalMeanRows 841).J/2-(generalMeanRows 841).error (generalMeanGrid j.val)+
      (generalMeanRows 841).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 841).c)).2-
      (generalMeanRows 841).J/2-(generalMeanRows 841).error 4 := by
  have he : (generalMeanRows 841).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 841) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 841)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0841

/-! Kernel-checked entropy margins for general spectral rectangle 842. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0842
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4950744461, 4780899574, 4618612458, 4463453846, 4315024785, 4172953986, 4036895466, 3906526432, 3781545386, 3661670414, 3546637651, 3436199881, 3330125274, 3228196242, 3130208390, 3035969564, 2945298980, 2858026426, 2773991529, 2693043089, 2615038454, 2539842959, 2467329397, 2397377534, 2329873666, 2264710202, 2201785278, 2141002406, 2082270141, 2025501773, 1970615044, 1917531879, 1866178141, 1816483400, 1768380715, 1721806437, 1676700014, 1633003824, 1590663004, 1549625297, 1509840911, 1471262379, 1433844435, 1397543896, 1362319547, 1328132037, 1294943783, 1262718871, 1231422976, 1201023276, 1171488374, 1142788226, 1114894074, 1087778377, 1061414756, 1035777929, 1010843663, 986588721, 962990810, 940028540, 917681377, 895929604, 874754283, 854137216, 834060911, 814508550, 795463958, 776911573, 758836418, 741224074, 724060655, 707332786, 691027579, 675132612, 659635907, 644525912, 629791484, 615421868, 601406687, 587735916, 574399876, 561389218, 548694904, 536308201, 524220666, 512424131, 500910699, 489672727, 478702817, 467993810, 457538773, 447330991, 437363960, 427631377, 418127136, 408845314, 399780172, 390926142, 382277824, 373829979, 365577524, 357515524, 349639189, 341943868, 334425046, 327078334, 319899471, 312884317, 306028847, 299329149, 292781421, 286381965, 280127187, 274013588, 268037769, 262196418, 256486315, 250904327, 245447404, 240112575, 234896949]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 842).prefactor = (1192622468680001/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 842).cutoff/(generalMeanRows 842).c)).2 =
    (148564257037/400000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 842).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 842).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 842).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 842

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 842).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 842).criticalRate j.val*(generalMeanRows 842).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 842).c*(generalMeanRows 842).criticalPoint j.val)).2-
      (generalMeanRows 842).J/2-(generalMeanRows 842).error (generalMeanGrid j.val)+
      (generalMeanRows 842).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 842).c)).2-
      (generalMeanRows 842).J/2-(generalMeanRows 842).error 4 := by
  have he : (generalMeanRows 842).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 842) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 842)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0842

/-! Kernel-checked entropy margins for general spectral rectangle 843. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0843
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5554893725, 5375689213, 5204263399, 5040177971, 4883025477, 4732426636, 4588027926, 4449499435, 4316532923, 4188840095, 4066151024, 3948212736, 3834787931, 3725653809, 3620601012, 3519432654, 3421963437, 3328018841, 3237434381, 3150054924, 3065734065, 2984333546, 2905722726, 2829778087, 2756382781, 2685426208, 2616803625, 2550415787, 2486168608, 2423972851, 2363743835, 2305401165, 2248868483, 2194073226, 2140946415, 2089422441, 2039438879, 1990936307, 1943858139, 1898150464, 1853761904, 1810643471, 1768748438, 1728032222, 1688452263, 1649967918, 1612540363, 1576132497, 1540708848, 1506235495, 1472679983, 1440011254, 1408199569, 1377216448, 1347034605, 1317627888, 1288971222, 1261040561, 1233812831, 1207265889, 1181378474, 1156130168, 1131501354, 1107473179, 1084027518, 1061146940, 1038814677, 1017014590, 995731146, 974949385, 954654898, 934833800, 915472707, 896558716, 878079381, 860022695, 842377070, 825131320, 808274641, 791796600, 775687114, 759936439, 744535154, 729474148, 714744608, 700338007, 686246091, 672460870, 658974604, 645779799, 632869191, 620235741, 607872627, 595773232, 583931138, 572340119, 560994135, 549887321, 539013985, 528368599, 517945794, 507740354, 497747210, 487961436, 478378243, 468992975, 459801103, 450798223, 441980048, 433342408, 424881245, 416592606, 408472646, 400517616, 392723869, 385087848, 377606092, 370275223, 363091953, 356053075, 349155462]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 843).prefactor = (2440349579756931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 843).cutoff/(generalMeanRows 843).c)).2 =
    (193962839105079/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 843).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 843).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 843).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 843

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 843).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 843).criticalRate j.val*(generalMeanRows 843).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 843).c*(generalMeanRows 843).criticalPoint j.val)).2-
      (generalMeanRows 843).J/2-(generalMeanRows 843).error (generalMeanGrid j.val)+
      (generalMeanRows 843).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 843).c)).2-
      (generalMeanRows 843).J/2-(generalMeanRows 843).error 4 := by
  have he : (generalMeanRows 843).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 843) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 843)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0843

/-! Kernel-checked entropy margins for general spectral rectangle 844. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0844
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5040773050, 4870194113, 4707150021, 4551214367, 4401990809, 4259110442, 4122229459, 3991027050, 3865203526, 3744478623, 3628589974, 3517291730, 3410353304, 3307558236, 3208703156, 3113596841, 3022059348, 2933921227, 2849022796, 2767213476, 2688351178, 2612301740, 2538938408, 2468141356, 2399797243, 2333798801, 2270044457, 2208437976, 2148888140, 2091308438, 2035616784, 1981735257, 1929589848, 1879110240, 1830229587, 1782884318, 1737013949, 1692560909, 1649470376, 1607690125, 1567170385, 1527863703, 1489724818, 1452710545, 1416779661, 1381892804, 1348012370, 1315102427, 1283128620, 1252058099, 1221859434, 1192502545, 1163958636, 1136200126, 1109200594, 1082934716, 1057378212, 1032507800, 1008301140, 984736793, 961794178, 939453528, 917695855, 896502911, 875857154, 855741716, 836140370, 817037504, 798418089, 780267657, 762572270, 745318504, 728493419, 712084542, 696079846, 680467730, 665236999, 650376851, 635876857, 621726945, 607917386, 594438783, 581282049, 568438405, 555899357, 543656692, 531702464, 520028983, 508628806, 497494725, 486619762, 475997156, 465620357, 455483017, 445578982, 435902287, 426447146, 417207947, 408179245, 399355758, 390732357, 382304064, 374066045, 366013606, 358142188, 350447359, 342924817, 335570376, 328379970, 321349646, 314475558, 307753967, 301181236, 294753827, 288468296, 282321292, 276309555, 270429910, 264679265, 259054611, 253553016]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 844).prefactor = (2375339260982931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 844).cutoff/(generalMeanRows 844).c)).2 =
    (46621682431661/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 844).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 844).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 844).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 844

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 844).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 844).criticalRate j.val*(generalMeanRows 844).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 844).c*(generalMeanRows 844).criticalPoint j.val)).2-
      (generalMeanRows 844).J/2-(generalMeanRows 844).error (generalMeanGrid j.val)+
      (generalMeanRows 844).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 844).c)).2-
      (generalMeanRows 844).J/2-(generalMeanRows 844).error 4 := by
  have he : (generalMeanRows 844).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 844) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 844)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0844

/-! Kernel-checked entropy margins for general spectral rectangle 845. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0845
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5376535858, 5195826796, 5023022810, 4857681358, 4699390898, 4547768176, 4402455815, 4263120155, 4129449313, 4001151445, 3877953169, 3759598150, 3645845807, 3536470145, 3431258695, 3330011536, 3232540414, 3138667925, 3048226776, 2961059100, 2877015825, 2795956097, 2717746747, 2642261795, 2569381997, 2498994421, 2430992057, 2365273453, 2301742377, 2240307505, 2180882130, 2123383889, 2067734507, 2013859567, 1961688283, 1911153298, 1862190488, 1814738785, 1768740004, 1724138687, 1680881954, 1638919365, 1598202786, 1558686268, 1520325933, 1483079862, 1446907996, 1411772038, 1377635364, 1344462935, 1312221220, 1280878117, 1250402885, 1220766071, 1191939455, 1163895980, 1136609703, 1110055736, 1084210197, 1059050165, 1034553630, 1010699451, 987467318, 964837708, 942791857, 921311716, 900379924, 879979775, 860095189, 840710684, 821811349, 803382818, 785411248, 767883295, 750786091, 734107228, 717834732, 701957049, 686463028, 671341899, 656583263, 642177072, 628113618, 614383516, 600977695, 587887380, 575104084, 562619597, 550425973, 538515517, 526880784, 515514560, 504409858, 493559907, 482958149, 472598222, 462473961, 452579386, 442908698, 433456270, 424216642, 415184514, 406354742, 397722332, 389282432, 381030331, 372961452, 365071347, 357355694, 349810290, 342431053, 335214009, 328155296, 321251158, 314497938, 307892081, 301430126, 295108705, 288924538, 282874433, 276955282]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 845).prefactor = (985922278471269/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 845).cutoff/(generalMeanRows 845).c)).2 =
    (22541064127997/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 845).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 845).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 845).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 845

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 845).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 845).criticalRate j.val*(generalMeanRows 845).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 845).c*(generalMeanRows 845).criticalPoint j.val)).2-
      (generalMeanRows 845).J/2-(generalMeanRows 845).error (generalMeanGrid j.val)+
      (generalMeanRows 845).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 845).c)).2-
      (generalMeanRows 845).J/2-(generalMeanRows 845).error 4 := by
  have he : (generalMeanRows 845).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 845) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 845)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0845

/-! Kernel-checked entropy margins for general spectral rectangle 846. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0846
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4958394176, 4786238901, 4621725912, 4464424880, 4313935680, 4169885758, 4031927779, 3899737525, 3773012005, 3651467755, 3534839311, 3422877817, 3315349773, 3212035890, 3112730056, 3017238384, 2925378347, 2836977990, 2751875196, 2669917026, 2590959100, 2514865034, 2441505919, 2370759840, 2302511428, 2236651451, 2173076432, 2111688294, 2052394029, 1995105395, 1939738634, 1886214198, 1834456514, 1784393742, 1735957570, 1689083005, 1643708191, 1599774231, 1557225020, 1516007096, 1476069491, 1437363600, 1399843048, 1363463577, 1328182927, 1293960736, 1260758441, 1228539178, 1197267704, 1166910305, 1137434725, 1108810087, 1081006828, 1053996632, 1027752368, 1002248032, 977458692, 953360436, 929930323, 907146337, 884987341, 863433038, 842463930, 822061283, 802207087, 782884028, 764075452, 745765339, 727938271, 710579405, 693674451, 677209643, 661171721, 645547902, 630325868, 615493739, 601040056, 586953764, 573224197, 559841056, 546794400, 534074627, 521672462, 509578941, 497785403, 486283474, 475065057, 464122321, 453447689, 443033831, 432873652, 422960283, 413287073, 403847583, 394635572, 385644995, 376869995, 368304892, 359944183, 351782528, 343814750, 336035828, 328440889, 321025205, 313784187, 306713379, 299808457, 293065220, 286479589, 280047601, 273765407, 267629264, 261635538, 255780694, 250061296, 244474005, 239015571, 233682837, 228472727, 223382254, 218408509]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 846).prefactor = (479606984612167/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 846).cutoff/(generalMeanRows 846).c)).2 =
    (353488536569337/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 846).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 846).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 846).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 846

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 846).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 846).criticalRate j.val*(generalMeanRows 846).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 846).c*(generalMeanRows 846).criticalPoint j.val)).2-
      (generalMeanRows 846).J/2-(generalMeanRows 846).error (generalMeanGrid j.val)+
      (generalMeanRows 846).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 846).c)).2-
      (generalMeanRows 846).J/2-(generalMeanRows 846).error 4 := by
  have he : (generalMeanRows 846).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 846) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 846)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0846

/-! Kernel-checked entropy margins for general spectral rectangle 847. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0847
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5201137735, 5032591807, 4871408679, 4717169462, 4569484970, 4427993126, 4292356640, 4162260938, 4037412295, 3917536162, 3802375655, 3691690183, 3585254209, 3482856126, 3384297227, 3289390772, 3197961133, 3109843011, 3024880719, 2942927524, 2863845041, 2787502674, 2713777104, 2642551814, 2573716648, 2507167409, 2442805480, 2380537476, 2320274920, 2261933944, 2205435008, 2150702640, 2097665194, 2046254622, 1996406267, 1948058664, 1901153355, 1855634720, 1811449813, 1768548216, 1726881893, 1686405060, 1647074063, 1608847261, 1571684914, 1535549084, 1500403537, 1466213656, 1432946350, 1400569979, 1369054276, 1338370279, 1308490262, 1279387670, 1251037065, 1223414066, 1196495297, 1170258340, 1144681683, 1119744680, 1095427506, 1071711120, 1048577225, 1026008235, 1003987240, 982497974, 961524785, 941052609, 921066940, 901553806, 882499745, 863891780, 845717401, 827964540, 810621557, 793677215, 777120667, 760941439, 745129410, 729674802, 714568165, 699800358, 685362542, 671246167, 657442957, 643944900, 630744241, 617833466, 605205296, 592852677, 580768774, 568946955, 557380793, 546064049, 534990672, 524154788, 513550696, 503172858, 493015898, 483074590, 473343859, 463818772, 454494533, 445366479, 436430076, 427680913, 419114698, 410727257, 402514525, 394472547, 386597470, 378885545, 371333118, 363936631, 356692617, 349597698, 342648581, 335842058, 329174998, 322644352, 316247144]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 847).prefactor = (4698631908177197/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 847).cutoff/(generalMeanRows 847).c)).2 =
    (24995868186219/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 847).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 847).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 847).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 847

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 847).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 847).criticalRate j.val*(generalMeanRows 847).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 847).c*(generalMeanRows 847).criticalPoint j.val)).2-
      (generalMeanRows 847).J/2-(generalMeanRows 847).error (generalMeanGrid j.val)+
      (generalMeanRows 847).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 847).c)).2-
      (generalMeanRows 847).J/2-(generalMeanRows 847).error 4 := by
  have he : (generalMeanRows 847).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 847) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 847)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0847

/-! Kernel-checked entropy margins for general spectral rectangle 848. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0848
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5017488975, 4845354287, 4680879263, 4523628848, 4373198709, 4229212552, 4091319730, 3959193098, 3832527093, 3711036002, 3594452400, 3482525739, 3375021065, 3271717855, 3172408959, 3076899633, 2985006654, 2896557516, 2811389686, 2729349921, 2650293651, 2574084392, 2500593222, 2429698289, 2361284353, 2295242374, 2231469114, 2169866785, 2110342709, 2052809006, 1997182309, 1943383492, 1891337418, 1840972707, 1792221516, 1745019336, 1699304802, 1655019512, 1612107865, 1570516900, 1530196152, 1491097515, 1453175114, 1416385181, 1380685948, 1346037532, 1312401842, 1279742484, 1248024667, 1217215127, 1187282044, 1158194969, 1129924755, 1102443493, 1075724444, 1049741989, 1024471567, 999889626, 975973575, 952701734, 930053293, 908008269, 886547469, 865652448, 845305480, 825489520, 806188175, 787385672, 769066832, 751217043, 733822232, 716868843, 700343815, 684234556, 668528928, 653215225, 638282151, 623718809, 609514679, 595659602, 582143770, 568957706, 556092251, 543538554, 531288058, 519332486, 507663833, 496274354, 485156551, 474303168, 463707179, 453361778, 443260375, 433396580, 423764205, 414357249, 405169893, 396196496, 387431584, 378869848, 370506135, 362335445, 354352924, 346553857, 338933668, 331487910, 324212264, 317102534, 310154640, 303364618, 296728616, 290242885, 283903781, 277707761, 271651377, 265731274, 259944190, 254286947, 248756455, 243349703, 238063762]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 848).prefactor = (4834804247632419/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 848).cutoff/(generalMeanRows 848).c)).2 =
    (148564257037/400000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 848).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 848).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 848).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 848

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 848).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 848).criticalRate j.val*(generalMeanRows 848).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 848).c*(generalMeanRows 848).criticalPoint j.val)).2-
      (generalMeanRows 848).J/2-(generalMeanRows 848).error (generalMeanGrid j.val)+
      (generalMeanRows 848).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 848).c)).2-
      (generalMeanRows 848).J/2-(generalMeanRows 848).error 4 := by
  have he : (generalMeanRows 848).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 848) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 848)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0848

/-! Kernel-checked entropy margins for general spectral rectangle 849. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0849
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5003868384, 4829938203, 4663780056, 4504952689, 4353045974, 4207678199, 4068493634, 3935160373, 3807368377, 3684827724, 3567267031, 3454432018, 3346084211, 3241999767, 3141968398, 3045792393, 2953285725, 2864273228, 2778589853, 2696079972, 2616596747, 2540001550, 2466163416, 2394958555, 2326269884, 2259986609, 2196003827, 2134222162, 2074547422, 2016890291, 1961166029, 1907294202, 1855198425, 1804806130, 1756048340, 1708859462, 1663177098, 1618941860, 1576097203, 1534589267, 1494366728, 1455380657, 1417584395, 1380933423, 1345385256, 1310899325, 1277436884, 1244960912, 1213436018, 1182828366, 1153105587, 1124236708, 1096192080, 1068943314, 1042463215, 1016725722, 991705855, 967379663, 943724168, 920717326, 898337974, 876565795, 855381273, 834765659, 814700932, 795169768, 776155506, 757642119, 739614181, 722056849, 704955826, 688297344, 672068139, 656255427, 640846885, 625830629, 611195198, 596929534, 583022965, 569465188, 556246257, 543356562, 530786823, 518528068, 506571629, 494909122, 483532440, 472433743, 461605443, 451040197, 440730898, 430670665, 420852832, 411270945, 401918749, 392790183, 383879373, 375180623, 366688410, 358397379, 350302333, 342398232, 334680183, 327143439, 319783389, 312595558, 305575600, 298719293, 292022536, 285481344, 279091846, 272850277, 266752980, 260796397, 254977070, 249291635, 243736821, 238309446, 233006413, 227824710, 222761404]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 849).prefactor = (489998568842921/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 849).cutoff/(generalMeanRows 849).c)).2 =
    (364417607101531/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 849).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 849).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 849).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 849

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 849).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 849).criticalRate j.val*(generalMeanRows 849).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 849).c*(generalMeanRows 849).criticalPoint j.val)).2-
      (generalMeanRows 849).J/2-(generalMeanRows 849).error (generalMeanGrid j.val)+
      (generalMeanRows 849).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 849).c)).2-
      (generalMeanRows 849).J/2-(generalMeanRows 849).error 4 := by
  have he : (generalMeanRows 849).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 849) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 849)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0849

/-! Kernel-checked entropy margins for general spectral rectangle 850. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0850
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5185671529, 5015254048, 4852309331, 4696412608, 4547169198, 4404211880, 4267198543, 4135810090, 4009748545, 3888735364, 3772509895, 3660828000, 3553460794, 3450193505, 3350824436, 3255164020, 3163033949, 3074266385, 2988703236, 2906195481, 2826602568, 2749791838, 2675638014, 2604022712, 2534834003, 2467965998, 2403318470, 2340796498, 2280310142, 2221774137, 2165107607, 2110233807, 2057079875, 2005576601, 1955658216, 1907262190, 1860329051, 1814802206, 1770627776, 1727754453, 1686133346, 1645717855, 1606463542, 1568328015, 1531270814, 1495253312, 1460238614, 1426191467, 1393078174, 1360866510, 1329525650, 1299026093, 1269339597, 1240439115, 1212298733, 1184893614, 1158199945, 1132194888, 1106856529, 1082163833, 1058096605, 1034635448, 1011761721, 989457510, 967705589, 946489390, 925792970, 905600986, 885898663, 866671773, 847906605, 829589949, 811709065, 794251668, 777205908, 760560348, 744303950, 728426053, 712916361, 697764927, 682962136, 668498695, 654365614, 640554201, 627056043, 613862998, 600967185, 588360971, 576036964, 563988001, 552207139, 540687651, 529423012, 518406894, 507633160, 497095852, 486789192, 476707566, 466845528, 457197785, 447759198, 438524772, 429489654, 420649127, 411998605, 403533628, 395249859, 387143079, 379209184, 371444178, 363844175, 356405389, 349124137, 341996830, 335019974, 328190165, 321504087, 314958509, 308550281, 302276335, 296133679]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 850).prefactor = (4761673933131317/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 850).cutoff/(generalMeanRows 850).c)).2 =
    (392841662670013/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 850).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 850).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 850).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 850

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 850).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 850).criticalRate j.val*(generalMeanRows 850).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 850).c*(generalMeanRows 850).criticalPoint j.val)).2-
      (generalMeanRows 850).J/2-(generalMeanRows 850).error (generalMeanGrid j.val)+
      (generalMeanRows 850).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 850).c)).2-
      (generalMeanRows 850).J/2-(generalMeanRows 850).error 4 := by
  have he : (generalMeanRows 850).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 850) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 850)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0850

/-! Kernel-checked entropy margins for general spectral rectangle 851. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0851
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5170624579, 4998347588, 4833654458, 4676114431, 4525327232, 4380920403, 4242546927, 4109883100, 3982626623, 3860494881, 3743223391, 3630564402, 3522285622, 3418169062, 3318009983, 3221615939, 3128805900, 3039409445, 2953266034, 2870224327, 2790141565, 2712882997, 2638321352, 2566336356, 2496814277, 2429647511, 2364734198, 2301977859, 2241287071, 2182575151, 2125759874, 2070763206, 2017511053, 1965933028, 1915962240, 1867535085, 1820591063, 1775072598, 1730924875, 1688095685, 1646535276, 1606196226, 1567033308, 1529003374, 1492065243, 1456179593, 1421308866, 1387417173, 1354470207, 1322435158, 1291280642, 1260976620, 1231494335, 1202806247, 1174885967, 1147708205, 1121248713, 1095484235, 1070392454, 1045951955, 1022142171, 998943352, 976336521, 954303436, 932826560, 911889026, 891474605, 871567679, 852153209, 833216715, 814744244, 796722353, 779138080, 761978929, 745232844, 728888193, 712933751, 697358677, 682152506, 667305125, 652806763, 638647975, 624819631, 611312899, 598119236, 585230375, 572638315, 560335311, 548313859, 536566695, 525086777, 513867282, 502901597, 492183309, 481706199, 471464233, 461451559, 451662495, 442091528, 432733304, 423582623, 414634437, 405883839, 397326063, 388956476, 380770574, 372763980, 364932434, 357271798, 349778041, 342447246, 335275599, 328259387, 321394998, 314678915, 308107711, 301678053, 295386689, 289230457, 283206272, 277311130]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 851).prefactor = (482556179938307/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 851).cutoff/(generalMeanRows 851).c)).2 =
    (385799380044601/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 851).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 851).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 851).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 851

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 851).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 851).criticalRate j.val*(generalMeanRows 851).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 851).c*(generalMeanRows 851).criticalPoint j.val)).2-
      (generalMeanRows 851).J/2-(generalMeanRows 851).error (generalMeanGrid j.val)+
      (generalMeanRows 851).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 851).c)).2-
      (generalMeanRows 851).J/2-(generalMeanRows 851).error 4 := by
  have he : (generalMeanRows 851).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 851) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 851)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0851

/-! Kernel-checked entropy margins for general spectral rectangle 852. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0852
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5193024164, 5024066148, 4862526440, 4707980021, 4560032168, 4418315804, 4282489130, 4152233507, 4027251552, 3907265427, 3792015293, 3681257908, 3574765363, 3472323930, 3373733009, 3278804175, 3187360303, 3099234769, 3014270712, 2932320368, 2853244446, 2776911559, 2703197699, 2631985755, 2563165058, 2496630974, 2432284517, 2370031993, 2309784670, 2251458472, 2194973695, 2140254739, 2087229866, 2035830964, 1985993339, 1937655508, 1890759019, 1845248272, 1801070358, 1758174903, 1716513932, 1676041727, 1636714706, 1598491307, 1561331873, 1525198551, 1490055198, 1455867282, 1422601804, 1390227212, 1358713329, 1328031278, 1298153418, 1269053278, 1240705498, 1213085775, 1186170808, 1159938248, 1134366652, 1109435435, 1085124835, 1061415865, 1038290282, 1015730548, 993719799, 972241809, 951280966, 930822240, 910851154, 891353765, 872316634, 853726806, 835571788, 817839527, 800518393, 783597161, 767064988, 750911403, 735126288, 719699864, 704622676, 689885578, 675479724, 661396553, 647627779, 634165378, 621001578, 608128851, 595539900, 583227653, 571185253, 559406050, 547883592, 536611620, 525584058, 514795008, 504238743, 493909700, 483802476, 473911820, 464232629, 454759941, 445488934, 436414917, 427533326, 418839724, 410329790, 401999321, 393844224, 385860515, 378044314, 370391842, 362899419, 355563458, 348380465, 341347034, 334459845, 327715663, 321111331, 314643774, 308309991]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 852).prefactor = (2391298771638893/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 852).cutoff/(generalMeanRows 852).c)).2 =
    (408272235896657/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 852).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 852).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 852).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 852

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 852).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 852).criticalRate j.val*(generalMeanRows 852).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 852).c*(generalMeanRows 852).criticalPoint j.val)).2-
      (generalMeanRows 852).J/2-(generalMeanRows 852).error (generalMeanGrid j.val)+
      (generalMeanRows 852).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 852).c)).2-
      (generalMeanRows 852).J/2-(generalMeanRows 852).error 4 := by
  have he : (generalMeanRows 852).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 852) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 852)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0852

/-! Kernel-checked entropy margins for general spectral rectangle 853. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0853
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7287348213, 7085564560, 6891707675, 6705362014, 6526140614, 6353682524, 6187650521, 6027729091, 5873622619, 5725053773, 5581762056, 5443502499, 5310044484, 5181170677, 5056676068, 4936367088, 4820060811, 4707584228, 4598773574, 4493473722, 4391537619, 4292825773, 4197205774, 4104551858, 4014744503, 3927670049, 3843220360, 3761292492, 3681788401, 3604614659, 3529682199, 3456906072, 3386205219, 3317502265, 3250723317, 3185797781, 3122658190, 3061240042, 3001481646, 2943323979, 2886710555, 2831587292, 2777902401, 2725606264, 2674651338, 2624992049, 2576584697, 2529387372, 2483359866, 2438463593, 2394661516, 2351918073, 2310199113, 2269471826, 2229704691, 2190867407, 2152930851, 2115867014, 2079648960, 2044250776, 2009647528, 1975815217, 1942730742, 1910371857, 1878717140, 1847745953, 1817438413, 1787775356, 1758738312, 1730309474, 1702471667, 1675208328, 1648503479, 1622341700, 1596708111, 1571588347, 1546968538, 1522835291, 1499175668, 1475977172, 1453227724, 1430915653, 1409029675, 1387558880, 1366492718, 1345820984, 1325533805, 1305621628, 1286075208, 1266885593, 1248044117, 1229542390, 1211372283, 1193525920, 1175995671, 1158774142, 1141854164, 1125228786, 1108891269, 1092835076, 1077053865, 1061541482, 1046291956, 1031299489, 1016558455, 1002063389, 987808981, 973790077, 960001666, 946438879, 933096986, 919971384, 907057601, 894351287, 881848208, 869544249, 857435402, 845517768, 833787550, 822241054, 810874679]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 853).prefactor = (465923488069613/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 853).cutoff/(generalMeanRows 853).c)).2 =
    (344605219851417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 853).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 853).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 853).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 853

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 853).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 853).criticalRate j.val*(generalMeanRows 853).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 853).c*(generalMeanRows 853).criticalPoint j.val)).2-
      (generalMeanRows 853).J/2-(generalMeanRows 853).error (generalMeanGrid j.val)+
      (generalMeanRows 853).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 853).c)).2-
      (generalMeanRows 853).J/2-(generalMeanRows 853).error 4 := by
  have he : (generalMeanRows 853).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 853) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 853)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0853

/-! Kernel-checked entropy margins for general spectral rectangle 854. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0854
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7523991552, 7312229823, 7108798503, 6913261553, 6725212911, 6544273788, 6370090286, 6202331270, 6040686476, 5884864814, 5734592847, 5589613424, 5449684444, 5314577740, 5184078066, 5057982176, 4936097989, 4818243817, 4704247676, 4593946634, 4487186233, 4383819938, 4283708647, 4186720228, 4092729094, 4001615810, 3913266730, 3827573660, 3744433541, 3663748159, 3585423874, 3509371365, 3435505396, 3363744590, 3294011228, 3226231051, 3160333081, 3096249451, 3033915245, 2973268346, 2914249298, 2856801174, 2800869445, 2746401869, 2693348379, 2641660972, 2591293620, 2542202168, 2494344251, 2447679206, 2402167998, 2357773143, 2314458634, 2272189879, 2230933633, 2190657943, 2151332082, 2112926504, 2075412784, 2038763577, 2002952563, 1967954409, 1933744722, 1900300014, 1867597656, 1835615851, 1804333592, 1773730631, 1743787448, 1714485220, 1685805794, 1657731657, 1630245913, 1603332255, 1576974942, 1551158777, 1525869086, 1501091695, 1476812913, 1453019507, 1429698693, 1406838112, 1384425814, 1362450245, 1340900228, 1319764953, 1299033959, 1278697122, 1258744643, 1239167036, 1219955114, 1201099979, 1182593012, 1164425864, 1146590442, 1129078901, 1111883637, 1094997278, 1078412673, 1062122884, 1046121183, 1030401039, 1014956114, 999780255, 984867489, 970212014, 955808196, 941650560, 927733788, 914052710, 900602302, 887377679, 874374091, 861586919, 849011668, 836643966, 824479559, 812514307, 800744178, 789165248, 777773696]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 854).prefactor = (978068251740513/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 854).cutoff/(generalMeanRows 854).c)).2 =
    (20967046018009/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 854).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 854).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 854).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 854

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 854).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 854).criticalRate j.val*(generalMeanRows 854).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 854).c*(generalMeanRows 854).criticalPoint j.val)).2-
      (generalMeanRows 854).J/2-(generalMeanRows 854).error (generalMeanGrid j.val)+
      (generalMeanRows 854).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 854).c)).2-
      (generalMeanRows 854).J/2-(generalMeanRows 854).error 4 := by
  have he : (generalMeanRows 854).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 854) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 854)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0854

/-! Kernel-checked entropy margins for general spectral rectangle 855. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0855
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7089824539, 6885753541, 6689815242, 6501580713, 6320650510, 6146652039, 5979237217, 5818080391, 5662876482, 5513339323, 5369200160, 5230206312, 5096119956, 4966717023, 4841786205, 4721128048, 4604554121, 4491886265, 4382955902, 4277603399, 4175677490, 4077034737, 3981539041, 3889061185, 3799478413, 3712674044, 3628537107, 3546962009, 3467848223, 3391100000, 3316626097, 3244339528, 3174157328, 3106000335, 3039792983, 2975463114, 2912941793, 2852163142, 2793064185, 2735584691, 2679667045, 2625256105, 2572299088, 2520745448, 2470546767, 2421656653, 2374030639, 2327626095, 2282402135, 2238319540, 2195340676, 2153429422, 2112551100, 2072672406, 2033761351, 1995787199, 1958720412, 1922532594, 1887196441, 1852685695, 1818975094, 1786040333, 1753858016, 1722405623, 1691661469, 1661604668, 1632215102, 1603473383, 1575360827, 1547859423, 1520951806, 1494621227, 1468851529, 1443627126, 1418932974, 1394754553, 1371077844, 1347889311, 1325175877, 1302924911, 1281124206, 1259761965, 1238826785, 1218307638, 1198193859, 1178475135, 1159141484, 1140183248, 1121591080, 1103355930, 1085469033, 1067921904, 1050706320, 1033814316, 1017238171, 1000970402, 985003755, 969331195, 953945898, 938841245, 924010815, 909448374, 895147873, 881103437, 867309363, 853760112, 840450301, 827374702, 814528234, 801905957, 789503070, 777314903, 765336915, 753564688, 741993926, 730620445, 719440175, 708449154, 697643522, 687019523, 676573497]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 855).prefactor = (601552767906929/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 855).cutoff/(generalMeanRows 855).c)).2 =
    (338975366839347/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 855).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 855).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 855).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 855

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 855).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 855).criticalRate j.val*(generalMeanRows 855).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 855).c*(generalMeanRows 855).criticalPoint j.val)).2-
      (generalMeanRows 855).J/2-(generalMeanRows 855).error (generalMeanGrid j.val)+
      (generalMeanRows 855).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 855).c)).2-
      (generalMeanRows 855).J/2-(generalMeanRows 855).error 4 := by
  have he : (generalMeanRows 855).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 855) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 855)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0855

/-! Kernel-checked entropy margins for general spectral rectangle 856. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0856
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6781415196, 6585592165, 6397659006, 6217195308, 6043809616, 5877136852, 5716836036, 5562588248, 5414094806, 5271075642, 5133267832, 5000424275, 4872312505, 4748713603, 4629421221, 4514240686, 4402988187, 4295490029, 4191581955, 4091108517, 3993922506, 3899884420, 3808861980, 3720729679, 3635368367, 3552664864, 3472511606, 3394806315, 3319451685, 3246355103, 3175428379, 3106587495, 3039752379, 2974846681, 2911797576, 2850535570, 2790994325, 2733110492, 2676823552, 2622075670, 2568811559, 2516978348, 2466525461, 2417404499, 2369569136, 2322975012, 2277579641, 2233342316, 2190224025, 2148187368, 2107196485, 2067216975, 2028215834, 1990161387, 1953023227, 1916772156, 1881380130, 1846820205, 1813066490, 1780094097, 1747879096, 1716398473, 1685630092, 1655552651, 1626145650, 1597389352, 1569264756, 1541753558, 1514838125, 1488501467, 1462727209, 1437499562, 1412803303, 1388623748, 1364946732, 1341758585, 1319046113, 1296796579, 1274997682, 1253637543, 1232704685, 1212188016, 1192076817, 1172360725, 1153029720, 1134074108, 1115484514, 1097251864, 1079367377, 1061822552, 1044609158, 1027719223, 1011145023, 994879075, 978914128, 963243151, 947859328, 932756048, 917926900, 903365662, 889066297, 875022944, 861229916, 847681686, 834372890, 821298315, 808452895, 795831709, 783429970, 771243027, 759266354, 747495552, 735926338, 724554546, 713376121, 702387117, 691583689, 680962095, 670518689, 660249920, 650152327]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 856).prefactor = (2359340191973429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 856).cutoff/(generalMeanRows 856).c)).2 =
    (176910937478171/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 856).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 856).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 856).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 856

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 856).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 856).criticalRate j.val*(generalMeanRows 856).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 856).c*(generalMeanRows 856).criticalPoint j.val)).2-
      (generalMeanRows 856).J/2-(generalMeanRows 856).error (generalMeanGrid j.val)+
      (generalMeanRows 856).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 856).c)).2-
      (generalMeanRows 856).J/2-(generalMeanRows 856).error 4 := by
  have he : (generalMeanRows 856).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 856) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 856)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0856

/-! Kernel-checked entropy margins for general spectral rectangle 857. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0857
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6028519377, 5828145969, 5636094894, 5451926556, 5275231395, 5105627221, 4942756855, 4786286013, 4635901428, 4491309160, 4352233081, 4218413505, 4089605951, 3965580030, 3846118421, 3731015952, 3620078751, 3513123481, 3409976633, 3310473876, 3214459464, 3121785692, 3032312387, 2945906445, 2862441399, 2781797023, 2703858957, 2628518372, 2555671643, 2485220060, 2417069542, 2351130390, 2287317039, 2225547834, 2165744824, 2107833558, 2051742908, 1997404890, 1944754504, 1893729583, 1844270643, 1796320759, 1749825426, 1704732446, 1660991817, 1618555620, 1577377922, 1537414683, 1498623662, 1460964336, 1424397818, 1388886781, 1354395385, 1320889214, 1288335204, 1256701587, 1225957832, 1196074588, 1167023633, 1138777827, 1111311059, 1084598206, 1058615089, 1033338435, 1008745835, 984815707, 961527265, 938860482, 916796059, 895315395, 874400560, 854034264, 834199832, 814881180, 796062793, 777729695, 759867436, 742462064, 725500111, 708968568, 692854873, 677146888, 661832889, 646901541, 632341892, 618143352, 604295684, 590788986, 577613681, 564760505, 552220495, 539984975, 528045551, 516394093, 505022735, 493923855, 483090074, 472514243, 462189436, 452108943, 442266259, 432655082, 423269300, 414102989, 405150402, 396405968, 387864282, 379520100, 371368334, 363404047, 355622447, 348018883, 340588838, 333327928, 326231896, 319296605, 312518038, 305892294, 299415579, 293084210, 286894606]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 857).prefactor = (4916144627974013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 857).cutoff/(generalMeanRows 857).c)).2 =
    (135904361647753/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 857).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 857).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 857).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 857

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 857).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 857).criticalRate j.val*(generalMeanRows 857).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 857).c*(generalMeanRows 857).criticalPoint j.val)).2-
      (generalMeanRows 857).J/2-(generalMeanRows 857).error (generalMeanGrid j.val)+
      (generalMeanRows 857).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 857).c)).2-
      (generalMeanRows 857).J/2-(generalMeanRows 857).error 4 := by
  have he : (generalMeanRows 857).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 857) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 857)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0857

/-! Kernel-checked entropy margins for general spectral rectangle 858. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0858
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5873606162, 5681846967, 5498090550, 5321909356, 5152905165, 4990706504, 4834966345, 4685360051, 4541583540, 4403351639, 4270396599, 4142466762, 4019325350, 3900749372, 3786528624, 3676464787, 3570370601, 3468069102, 3369392939, 3274183731, 3182291488, 3093574070, 3007896695, 2925131478, 2845157009, 2767857962, 2693124728, 2620853084, 2550943874, 2483302717, 2417839740, 2354469320, 2293109850, 2233683516, 2176116092, 2120336745, 2066277855, 2013874845, 1963066019, 1913792416, 1865997667, 1819627863, 1774631431, 1730959016, 1688563371, 1647399251, 1607423320, 1568594052, 1530871647, 1494217948, 1458596359, 1423971779, 1390310524, 1357580265, 1325749963, 1294789812, 1264671182, 1235366562, 1206849516, 1179094627, 1152077460, 1125774509, 1100163166, 1075221672, 1050929087, 1027265252, 1004210756, 981746900, 959855673, 938519720, 917722312, 897447323, 877679203, 858402956, 839604115, 821268722, 803383305, 785934861, 768910835, 752299104, 736087956, 720266079, 704822540, 689746774, 675028567, 660658043, 646625652, 632922156, 619538619, 606466393, 593697107, 581222660, 569035208, 557127154, 545491140, 534120040, 523006946, 512145166, 501528214, 491149799, 481003825, 471084377, 461385719, 451902286, 442628679, 433559658, 424690137, 416015177, 407529985, 399229904, 391110414, 383167121, 375395756, 367792174, 360352343, 353072345, 345948372, 338976719, 332153785, 325476068, 318940159]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 858).prefactor = (4790073063501939/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 858).cutoff/(generalMeanRows 858).c)).2 =
    (302626519837619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 858).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 858).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 858).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 858

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 858).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 858).criticalRate j.val*(generalMeanRows 858).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 858).c*(generalMeanRows 858).criticalPoint j.val)).2-
      (generalMeanRows 858).J/2-(generalMeanRows 858).error (generalMeanGrid j.val)+
      (generalMeanRows 858).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 858).c)).2-
      (generalMeanRows 858).J/2-(generalMeanRows 858).error 4 := by
  have he : (generalMeanRows 858).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 858) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 858)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0858

/-! Kernel-checked entropy margins for general spectral rectangle 859. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0859
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5867960500, 5684671914, 5509027365, 5340612482, 5179041537, 5023954922, 4875016906, 4731913638, 4594351350, 4462054752, 4334765583, 4212241302, 4094253909, 3980588869, 3871044139, 3765429275, 3663564627, 3565280593, 3470416941, 3378822185, 3290353011, 3204873748, 3122255885, 3042377615, 2965123424, 2890383703, 2818054392, 2748036649, 2680236541, 2614564757, 2550936340, 2489270442, 2429490088, 2371521960, 2315296194, 2260746193, 2207808444, 2156422357, 2106530106, 2058076480, 2011008753, 1965276545, 1920831709, 1877628210, 1835622023, 1794771026, 1755034908, 1716375079, 1678754580, 1642138012, 1606491449, 1571782374, 1537979610, 1505053254, 1472974617, 1441716166, 1411251474, 1381555161, 1352602852, 1324371128, 1296837481, 1269980275, 1243778705, 1218212759, 1193263185, 1168911454, 1145139731, 1121930841, 1099268245, 1077136006, 1055518769, 1034401732, 1013770625, 993611684, 973911633, 954657663, 935837410, 917438937, 899450721, 881861630, 864660908, 847838164, 831383352, 815286761, 799539000, 784130983, 769053921, 754299310, 739858916, 725724767, 711889144, 698344570, 685083800, 672099814, 659385806, 646935179, 634741535, 622798669, 611100560, 599641367, 588415419, 577417213, 566641404, 556082802, 545736366, 535597196, 525660533, 515921751, 506376351, 497019961, 487848328, 478857314, 470042895, 461401155, 452928282, 444620565, 436474394, 428486250, 420652708, 412970431, 405436168]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 859).prefactor = (4655976769688803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 859).cutoff/(generalMeanRows 859).c)).2 =
    (86769570602113/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 859).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 859).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 859).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 859

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 859).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 859).criticalRate j.val*(generalMeanRows 859).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 859).c*(generalMeanRows 859).criticalPoint j.val)).2-
      (generalMeanRows 859).J/2-(generalMeanRows 859).error (generalMeanGrid j.val)+
      (generalMeanRows 859).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 859).c)).2-
      (generalMeanRows 859).J/2-(generalMeanRows 859).error 4 := by
  have he : (generalMeanRows 859).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 859) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 859)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0859

/-! Kernel-checked entropy margins for general spectral rectangle 860. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0860
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5423797663, 5244138701, 5072124505, 4907339382, 4749396337, 4597934559, 4452617181, 4313129273, 4179176053, 4050481277, 3926785788, 3807846207, 3693433744, 3583333130, 3477341632, 3375268165, 3276932479, 3182164411, 3090803207, 3002696895, 2917701705, 2835681544, 2756507506, 2680057415, 2606215414, 2534871576, 2465921540, 2399266187, 2334811323, 2272467394, 2212149218, 2153775734, 2097269770, 2042557823, 1989569857, 1938239112, 1888501925, 1840297564, 1793568070, 1748258111, 1704314841, 1661687775, 1620328664, 1580191378, 1541231803, 1503407735, 1466678787, 1431006296, 1396353239, 1362684151, 1329965052, 1298163372, 1267247885, 1237188644, 1207956918, 1179525141, 1151866849, 1124956635, 1098770099, 1073283797, 1048475203, 1024322666, 1000805368, 977903287, 955597166, 933868471, 912699367, 892072683, 871971883, 852381041, 833284812, 814668408, 796517576, 778818572, 761558142, 744723502, 728302314, 712282675, 696653090, 681402465, 666520083, 651995591, 637818987, 623980606, 610471102, 597281442, 584402890, 571826993, 559545576, 547550728, 535834789, 524390346, 513210221, 502287460, 491615329, 481187302, 470997054, 461038457, 451305567, 441792623, 432494036, 423404385, 414518412, 405831011, 397337230, 389032260, 380911433, 372970216, 365204204, 357609121, 350180812, 342915237, 335808472, 328856702, 322056217, 315403413, 308894779, 302526907, 296296475, 290200257, 284235108]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 860).prefactor = (2332035666528919/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 860).cutoff/(generalMeanRows 860).c)).2 =
    (324432505926531/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 860).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 860).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 860).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 860

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 860).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 860).criticalRate j.val*(generalMeanRows 860).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 860).c*(generalMeanRows 860).criticalPoint j.val)).2-
      (generalMeanRows 860).J/2-(generalMeanRows 860).error (generalMeanGrid j.val)+
      (generalMeanRows 860).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 860).c)).2-
      (generalMeanRows 860).J/2-(generalMeanRows 860).error 4 := by
  have he : (generalMeanRows 860).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 860) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 860)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0860

/-! Kernel-checked entropy margins for general spectral rectangle 861. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0861
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5467169195, 5296230293, 5132530521, 4975669552, 4825275002, 4680999980, 4542520905, 4409535556, 4281761331, 4158933668, 4040804635, 3927141651, 3817726323, 3712353399, 3610829809, 3512973794, 3418614107, 3327589288, 3239746991, 3154943375, 3073042538, 2993915995, 2917442203, 2843506116, 2771998777, 2702816937, 2635862705, 2571043224, 2508270363, 2447460442, 2388533963, 2331415372, 2276032826, 2222317983, 2170205805, 2119634368, 2070544691, 2022880574, 1976588444, 1931617211, 1887918137, 1845444709, 1804152520, 1763999158, 1724944102, 1686948625, 1649975697, 1613989905, 1578957365, 1544845645, 1511623695, 1479261779, 1447731402, 1417005260, 1387057173, 1357862034, 1329395757, 1301635229, 1274558259, 1248143540, 1222370605, 1197219787, 1172672181, 1148709612, 1125314599, 1102470323, 1080160599, 1058369845, 1037083057, 1016285781, 995964090, 976104563, 956694258, 937720695, 919171833, 901036056, 883302148, 865959283, 848997003, 832405206, 816174130, 800294338, 784756707, 769552413, 754672920, 740109967, 725855560, 711901957, 698241663, 684867416, 671772180, 658949136, 646391673, 634093383, 622048048, 610249638, 598692299, 587370352, 576278283, 565410737, 554762513, 544328558, 534103964, 524083959, 514263904, 504639290, 495205731, 485958960, 476894826, 468009290, 459298420, 450758390, 442385473, 434176039, 426126554, 418233575, 410493745, 402903795, 395460536, 388160862, 381001743]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 861).prefactor = (4513789476004569/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 861).cutoff/(generalMeanRows 861).c)).2 =
    (375784954006769/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 861).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 861).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 861).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 861

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 861).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 861).criticalRate j.val*(generalMeanRows 861).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 861).c*(generalMeanRows 861).criticalPoint j.val)).2-
      (generalMeanRows 861).J/2-(generalMeanRows 861).error (generalMeanGrid j.val)+
      (generalMeanRows 861).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 861).c)).2-
      (generalMeanRows 861).J/2-(generalMeanRows 861).error 4 := by
  have he : (generalMeanRows 861).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 861) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 861)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0861

/-! Kernel-checked entropy margins for general spectral rectangle 862. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0862
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5084766409, 4917736110, 4757903507, 4604869017, 4458260964, 4317733134, 4182962603, 4053647791, 3929506719, 3810275436, 3695706613, 3585568259, 3479642562, 3377724845, 3279622599, 3185154622, 3094150211, 3006448442, 2921897495, 2840354045, 2761682694, 2685755452, 2612451259, 2541655540, 2473259796, 2407161227, 2343262378, 2281470813, 2221698813, 2163863095, 2107884550, 2053687995, 2001201949, 1950358421, 1901092709, 1853343215, 1807051273, 1762160985, 1718619068, 1676374714, 1635379456, 1595587040, 1556953308, 1519436088, 1482995091, 1447591809, 1413189428, 1379752736, 1347248045, 1315643114, 1284907073, 1255010357, 1225924641, 1197622780, 1170078748, 1143267587, 1117165354, 1091749070, 1066996681, 1042887006, 1019399700, 996515216, 974214765, 952480282, 931294395, 910640390, 890502184, 870864293, 851711811, 833030379, 814806162, 797025829, 779676526, 762745861, 746221879, 730093047, 714348234, 698976695, 683968054, 669312290, 654999721, 641020989, 627367051, 614029161, 600998863, 588267974, 575828579, 563673014, 551793863, 540183943, 528836298, 517744187, 506901081, 496300650, 485936758, 475803455, 465894970, 456205705, 446730228, 437463269, 428399710, 419534584, 410863065, 402380469, 394082243, 385963964, 378021335, 370250176, 362646426, 355206135, 347925462, 340800671, 333828127, 327004292, 320325725, 313789074, 307391079, 301128564, 294998436, 288997683, 283123372]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 862).prefactor = (1126014830512147/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 862).cutoff/(generalMeanRows 862).c)).2 =
    (45031595660829/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 862).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 862).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 862).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 862

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 862).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 862).criticalRate j.val*(generalMeanRows 862).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 862).c*(generalMeanRows 862).criticalPoint j.val)).2-
      (generalMeanRows 862).J/2-(generalMeanRows 862).error (generalMeanGrid j.val)+
      (generalMeanRows 862).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 862).c)).2-
      (generalMeanRows 862).J/2-(generalMeanRows 862).error 4 := by
  have he : (generalMeanRows 862).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 862) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 862)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0862

/-! Kernel-checked entropy margins for general spectral rectangle 863. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0863
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4961568959, 4790687952, 4627289590, 4470958746, 4321309190, 4177981061, 4040638623, 3908968248, 3782676617, 3661489097, 3545148277, 3433412648, 3326055406, 3222863363, 3123635959, 3028184358, 2936330626, 2847906975, 2762755071, 2680725399, 2601676683, 2525475339, 2451994989, 2381115996, 2312725039, 2246714728, 2182983230, 2121433942, 2061975166, 2004519827, 1948985196, 1895292638, 1843367374, 1793138266, 1744537606, 1697500925, 1651966813, 1607876752, 1565174957, 1523808226, 1483725802, 1444879247, 1407222312, 1370710828, 1335302593, 1300957275, 1267636311, 1235302822, 1203921523, 1173458646, 1143881862, 1115160212, 1087264038, 1060164918, 1033835610, 1008249991, 983383007, 959210616, 935709748, 912858254, 890634863, 869019143, 847991463, 827532954, 807625475, 788251580, 769394488, 751038051, 733166727, 715765554, 698820124, 682316556, 666241479, 650582005, 635325710, 620460614, 605975163, 591858210, 578098999, 564687147, 551612631, 538865773, 526437222, 514317947, 502499217, 490972598, 479729930, 468763328, 458065161, 447628048, 437444848, 427508648, 417812756, 408350692, 399116182, 390103147, 381305698, 372718128, 364334907, 356150671, 348160223, 340358519, 332740670, 325301932, 318037700, 310943507, 304015016, 297248019, 290638426, 284182268, 277875690, 271714945, 265696395, 259816504, 254071834, 248459044, 242974887, 237616204, 232379925, 227263063, 222262713]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 863).prefactor = (1159400594592861/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 863).cutoff/(generalMeanRows 863).c)).2 =
    (335560152696259/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 863).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 863).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 863).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 863

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 863).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 863).criticalRate j.val*(generalMeanRows 863).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 863).c*(generalMeanRows 863).criticalPoint j.val)).2-
      (generalMeanRows 863).J/2-(generalMeanRows 863).error (generalMeanGrid j.val)+
      (generalMeanRows 863).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 863).c)).2-
      (generalMeanRows 863).J/2-(generalMeanRows 863).error 4 := by
  have he : (generalMeanRows 863).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 863) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 863)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0863

/-! Kernel-checked entropy margins for general spectral rectangle 864. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0864
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5163267915, 4995779992, 4835532190, 4682118971, 4535163268, 4394314002, 4259243855, 4129647289, 4005238764, 3885751132, 3770934198, 3660553410, 3554388673, 3452233280, 3353892927, 3259184824, 3167936880, 3079986956, 2995182179, 2913378319, 2834439205, 2758236197, 2684647696, 2613558688, 2544860327, 2478449546, 2414228699, 2352105228, 2291991349, 2233803771, 2177463422, 2122895204, 2070027757, 2018793244, 1969127149, 1920968087, 1874257626, 1828940122, 1784962566, 1742274437, 1700827565, 1660576005, 1621475916, 1583485450, 1546564644, 1510675323, 1475781004, 1441846809, 1408839383, 1376726817, 1345478570, 1315065403, 1285459314, 1256633475, 1228562175, 1201220763, 1174585597, 1148633998, 1123344197, 1098695298, 1074667232, 1051240721, 1028397237, 1006118970, 984388795, 963190237, 942507444, 922325160, 902628692, 883403893, 864637129, 846315265, 828425634, 810956024, 793894654, 777230157, 760951562, 745048277, 729510071, 714327064, 699489706, 684988769, 670815329, 656960756, 643416702, 630175090, 617228102, 604568169, 592187961, 580080379, 568238544, 556655790, 545325655, 534241874, 523398370, 512789250, 502408795, 492251454, 482311841, 472584723, 463065021, 453747800, 444628267, 435701763, 426963760, 418409855, 410035770, 401837342, 393810521, 385951368, 378256051, 370720839, 363342101, 356116300, 349039995, 342109833, 335322547, 328674957, 322163961, 315786538, 309539745]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 864).prefactor = (4554164027253597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 864).cutoff/(generalMeanRows 864).c)).2 =
    (378142330037407/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 864).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 864).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 864).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 864

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 864).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 864).criticalRate j.val*(generalMeanRows 864).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 864).c*(generalMeanRows 864).criticalPoint j.val)).2-
      (generalMeanRows 864).J/2-(generalMeanRows 864).error (generalMeanGrid j.val)+
      (generalMeanRows 864).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 864).c)).2-
      (generalMeanRows 864).J/2-(generalMeanRows 864).error 4 := by
  have he : (generalMeanRows 864).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 864) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 864)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0864

/-! Kernel-checked entropy margins for general spectral rectangle 865. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0865
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5160850629, 4991321027, 4829096822, 4673772452, 4524970677, 4382340106, 4245552981, 4114303209, 3988304593, 3867289232, 3751006097, 3639219723, 3531709043, 3428266313, 3328696147, 3232814629, 3140448504, 3051434439, 2965618342, 2882854744, 2803006220, 2725942866, 2651541810, 2579686762, 2510267601, 2443179988, 2378325009, 2315608846, 2254942468, 2196241345, 2139425183, 2084417675, 2031146272, 1979541964, 1929539081, 1881075104, 1834090487, 1788528497, 1744335055, 1701458593, 1659849916, 1619462079, 1580250264, 1542171668, 1505185397, 1469252370, 1434335220, 1400398209, 1367407146, 1335329304, 1304133355, 1273789289, 1244268359, 1215543012, 1187586835, 1160374494, 1133881688, 1108085097, 1082962333, 1058491901, 1034653150, 1011426242, 988792105, 966732406, 945229511, 924266456, 903826918, 883895183, 864456119, 845495154, 826998245, 808951861, 791342958, 774158956, 757387723, 741017553, 725037148, 709435602, 694202384, 679327323, 664800592, 650612694, 636754450, 623216984, 609991711, 597070327, 584444799, 572107349, 560050448, 548266807, 536749365, 525491281, 514485928, 503726881, 493207912, 482922982, 472866235, 463031988, 453414728, 444009106, 434809927, 425812151, 417010879, 408401356, 399978962, 391739208, 383677732, 375790292, 368072766, 360521145, 353131530, 345900129, 338823254, 331897313, 325118813, 318484353, 311990624, 305634402, 299412548, 293322005, 287359795]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 865).prefactor = (2285727161912603/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 865).cutoff/(generalMeanRows 865).c)).2 =
    (45031595660829/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 865).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 865).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 865).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 865

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 865).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 865).criticalRate j.val*(generalMeanRows 865).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 865).c*(generalMeanRows 865).criticalPoint j.val)).2-
      (generalMeanRows 865).J/2-(generalMeanRows 865).error (generalMeanGrid j.val)+
      (generalMeanRows 865).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 865).c)).2-
      (generalMeanRows 865).J/2-(generalMeanRows 865).error 4 := by
  have he : (generalMeanRows 865).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 865) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 865)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0865

/-! Kernel-checked entropy margins for general spectral rectangle 866. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0866
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4995117300, 4824433764, 4661193595, 4504984216, 4355421776, 4212148640, 4074831159, 3943157661, 3816836663, 3695595258, 3579177656, 3467343876, 3359868551, 3256539847, 3157158480, 3061536819, 2969498065, 2880875502, 2795511807, 2713258424, 2633974975, 2557528732, 2483794122, 2412652267, 2343990570, 2277702317, 2213686320, 2151846581, 2092091979, 2034335978, 1978496363, 1924494982, 1872257515, 1821713253, 1772794896, 1725438360, 1679582599, 1635169435, 1592143406, 1550451613, 1510043589, 1470871160, 1432888335, 1396051181, 1360317721, 1325647832, 1292003152, 1259346983, 1227644215, 1196861242, 1166965888, 1137927334, 1109716053, 1082303750, 1055663294, 1029768671, 1004594921, 980118099, 956315214, 933164197, 910643848, 888733800, 867414482, 846667078, 826473496, 806816335, 787678853, 769044938, 750899078, 733226339, 716012336, 699243209, 682905603, 666986644, 651473917, 636355452, 621619699, 607255515, 593252142, 579599198, 566286656, 553304829, 540644362, 528296212, 516251639, 504502195, 493039708, 481856275, 470944250, 460296236, 449905070, 439763821, 429865777, 420204436, 410773500, 401566870, 392578631, 383803052, 375234578, 366867822, 358697557, 350718716, 342926381, 335315782, 327882287, 320621401, 313528759, 306600124, 299831380, 293218528, 286757684, 280445075, 274277032, 268249990, 262360484, 256605143, 250980692, 245483944, 240111800, 234861243, 229729341]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 866).prefactor = (4639857768417453/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 866).cutoff/(generalMeanRows 866).c)).2 =
    (338975366839347/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 866).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 866).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 866).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 866

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 866).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 866).criticalRate j.val*(generalMeanRows 866).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 866).c*(generalMeanRows 866).criticalPoint j.val)).2-
      (generalMeanRows 866).J/2-(generalMeanRows 866).error (generalMeanGrid j.val)+
      (generalMeanRows 866).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 866).c)).2-
      (generalMeanRows 866).J/2-(generalMeanRows 866).error 4 := by
  have he : (generalMeanRows 866).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 866) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 866)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0866

/-! Kernel-checked entropy margins for general spectral rectangle 867. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0867
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5293700410, 5126758638, 4967006927, 4814040055, 4667481376, 4526980318, 4392210159, 4262866028, 4138663119, 4019335079, 3904632555, 3794321885, 3688183905, 3586012869, 3487615465, 3392809919, 3301425173, 3213300137, 3128283001, 3046230602, 2967007846, 2890487169, 2816548048, 2745076544, 2675964879, 2609111049, 2544418463, 2481795604, 2421155724, 2362416550, 2305500016, 2250332015, 2196842164, 2144963585, 2094632703, 2045789058, 1998375125, 1952336148, 1907619986, 1864176969, 1821959758, 1780923218, 1741024302, 1702221933, 1664476902, 1627751766, 1592010757, 1557219692, 1523345892, 1490358102, 1458226422, 1426922232, 1396418131, 1366687874, 1337706314, 1309449348, 1281893866, 1255017700, 1228799581, 1203219090, 1178256626, 1153893356, 1130111188, 1106892730, 1084221260, 1062080692, 1040455551, 1019330939, 998692515, 978526462, 958819473, 939558719, 920731832, 902326886, 884332374, 866737192, 849530620, 832702308, 816242257, 800140808, 784388621, 768976671, 753896226, 739138841, 724696342, 710560820, 696724614, 683180306, 669920710, 656938861, 644228010, 631781611, 619593318, 607656972, 595966601, 584516405, 573300756, 562314186, 551551387, 541007201, 530676616, 520554760, 510636898, 500918424, 491394859, 482061846, 472915146, 463950631, 455164287, 446552202, 438110568, 429835676, 421723914, 413771760, 405975784, 398332643, 390839076, 383491904, 376288029, 369224426, 362298147]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 867).prefactor = (2272903446990357/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 867).cutoff/(generalMeanRows 867).c)).2 =
    (398078889674661/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 867).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 867).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 867).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 867

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 867).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 867).criticalRate j.val*(generalMeanRows 867).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 867).c*(generalMeanRows 867).criticalPoint j.val)).2-
      (generalMeanRows 867).J/2-(generalMeanRows 867).error (generalMeanGrid j.val)+
      (generalMeanRows 867).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 867).c)).2-
      (generalMeanRows 867).J/2-(generalMeanRows 867).error 4 := by
  have he : (generalMeanRows 867).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 867) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 867)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0867

/-! Kernel-checked entropy margins for general spectral rectangle 868. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0868
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5244665504, 5076862705, 4916312075, 4762605329, 4615362942, 4474231639, 4338882149, 4209007198, 4084319707, 3964551178, 3849450225, 3738781259, 3632323286, 3529868825, 3431222911, 3336202201, 3244634139, 3156356210, 3071215245, 2989066781, 2909774485, 2833209609, 2759250496, 2687782123, 2618695675, 2551888154, 2487262015, 2424724831, 2364188976, 2305571337, 2248793043, 2193779213, 2140458719, 2088763970, 2038630705, 1989997804, 1942807106, 1897003247, 1852533500, 1809347628, 1767397751, 1726638210, 1687025456, 1648517926, 1611075946, 1574661623, 1539238758, 1504772751, 1471230522, 1438580430, 1406792202, 1375836860, 1345686658, 1316315019, 1287696475, 1259806615, 1232622032, 1206120271, 1180279788, 1155079899, 1130500747, 1106523253, 1083129087, 1060300631, 1038020942, 1016273723, 995043295, 974314566, 954073005, 934304617, 914995917, 896133911, 877706071, 859700314, 842104986, 824908840, 808101021, 791671045, 775608788, 759904469, 744548635, 729532147, 714846168, 700482150, 686431823, 672687182, 659240479, 646084210, 633211107, 620614128, 608286450, 596221455, 584412730, 572854053, 561539389, 550462881, 539618845, 529001763, 518606276, 508427179, 498459416, 488698074, 479138377, 469775683, 460605478, 451623372, 442825096, 434206494, 425763524, 417492250, 409388841, 401449568, 393670798, 386048993, 378580706, 371262578, 364091336, 357063791, 350176832, 343427428, 336812620]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 868).prefactor = (2288970088125931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 868).cutoff/(generalMeanRows 868).c)).2 =
    (390779587193049/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 868).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 868).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 868).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 868

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 868).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 868).criticalRate j.val*(generalMeanRows 868).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 868).c*(generalMeanRows 868).criticalPoint j.val)).2-
      (generalMeanRows 868).J/2-(generalMeanRows 868).error (generalMeanGrid j.val)+
      (generalMeanRows 868).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 868).c)).2-
      (generalMeanRows 868).J/2-(generalMeanRows 868).error 4 := by
  have he : (generalMeanRows 868).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 868) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 868)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0868

/-! Kernel-checked entropy margins for general spectral rectangle 869. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0869
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5200407280, 5031714617, 4870314154, 4715797434, 4567784679, 4425922285, 4289880579, 4159351826, 4034048430, 3913701324, 3798058513, 3686883756, 3579955377, 3477065180, 3378017465, 3282628128, 3190723838, 3102141290, 3016726513, 2934334237, 2854827314, 2778076179, 2703958356, 2632358005, 2563165497, 2496277024, 2431594237, 2369023911, 2308477634, 2249871513, 2193125908, 2138165180, 2084917458, 2033314416, 1983291073, 1934785603, 1887739153, 1842095681, 1797801795, 1754806610, 1713061611, 1672520521, 1633139186, 1594875455, 1557689078, 1521541605, 1486396290, 1452218007, 1418973160, 1386629608, 1355156592, 1324524663, 1294705617, 1265672435, 1237399218, 1209861139, 1183034387, 1156896118, 1131424407, 1106598209, 1082397309, 1058802291, 1035794494, 1013355980, 991469499, 970118460, 949286896, 928959441, 909121297, 889758214, 870856461, 852402807, 834384496, 816789227, 799605135, 782820770, 766425084, 750407406, 734757434, 719465216, 704521133, 689915891, 675640501, 661686272, 648044796, 634707937, 621667822, 608916826, 596447567, 584252895, 572325882, 560659813, 549248180, 538084673, 527163173, 516477741, 506022620, 495792217, 485781108, 475984023, 466395845, 457011606, 447826476, 438835764, 430034908, 421419476, 412985156, 404727756, 396643198, 388727515, 380976846, 373387433, 365955619, 358677843, 351550639, 344570628, 337734521, 331039114, 324481285, 318057990, 311766263]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 869).prefactor = (573365263862541/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 869).cutoff/(generalMeanRows 869).c)).2 =
    (378142330037407/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 869).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 869).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 869).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 869

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 869).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 869).criticalRate j.val*(generalMeanRows 869).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 869).c*(generalMeanRows 869).criticalPoint j.val)).2-
      (generalMeanRows 869).J/2-(generalMeanRows 869).error (generalMeanGrid j.val)+
      (generalMeanRows 869).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 869).c)).2-
      (generalMeanRows 869).J/2-(generalMeanRows 869).error 4 := by
  have he : (generalMeanRows 869).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 869) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 869)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0869

/-! Kernel-checked entropy margins for general spectral rectangle 870. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0870
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5154019910, 4984505973, 4822347188, 4667131905, 4518477347, 4376027087, 4239448795, 4108432232, 3982687437, 3861943106, 3745945127, 3634455256, 3527249914, 3424119101, 3324865402, 3229303082, 3137257261, 3048563155, 2963065384, 2880617338, 2801080585, 2724324338, 2650224955, 2578665476, 2509535205, 2442729314, 2378148476, 2315698530, 2255290166, 2196838634, 2140263471, 2085488248, 2032440336, 1981050684, 1931253616, 1882986636, 1836190250, 1790807798, 1746785299, 1704071299, 1662616737, 1622374813, 1583300868, 1545352267, 1508488297, 1472670060, 1437860382, 1404023722, 1371126088, 1339134960, 1308019212, 1277749043, 1248295910, 1219632469, 1191732510, 1164570906, 1138123556, 1112367341, 1087280070, 1062840440, 1039027994, 1015823078, 993206807, 971161024, 949668274, 928711762, 908275332, 888343434, 868901093, 849933891, 831427935, 813369839, 795746699, 778546072, 761755956, 745364773, 729361348, 713734895, 698474995, 683571590, 669014957, 654795703, 640904747, 627333307, 614072890, 601115280, 588452525, 576076930, 563981043, 552157647, 540599752, 529300585, 518253584, 507452384, 496890817, 486562900, 476462829, 466584974, 456923869, 447474211, 438230849, 429188784, 420343157, 411689251, 403222480, 394938388, 386832646, 378901041, 371139479, 363543978, 356110664, 348835768, 341715623, 334746659, 327925403, 321248470, 314712568, 308314489, 302051109, 295919384, 289916348]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 870).prefactor = (2309957911655901/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 870).cutoff/(generalMeanRows 870).c)).2 =
    (185474027201689/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 870).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 870).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 870).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 870

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 870).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 870).criticalRate j.val*(generalMeanRows 870).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 870).c*(generalMeanRows 870).criticalPoint j.val)).2-
      (generalMeanRows 870).J/2-(generalMeanRows 870).error (generalMeanGrid j.val)+
      (generalMeanRows 870).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 870).c)).2-
      (generalMeanRows 870).J/2-(generalMeanRows 870).error 4 := by
  have he : (generalMeanRows 870).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 870) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 870)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0870

/-! Kernel-checked entropy margins for general spectral rectangle 871. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0871
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5196479421, 5027845887, 4866526727, 4712110543, 4564214890, 4422483745, 4286585247, 4156209681, 4031067664, 3910888516, 3795418787, 3684420932, 3577672103, 3474963056, 3376097152, 3280889454, 3189165890, 3100762502, 3015524740, 2933306831, 2853971183, 2777387853, 2703434037, 2631993616, 2562956727, 2496219369, 2431683037, 2369254381, 2308844894, 2250370618, 2193751870, 2138912989, 2085782101, 2034290897, 1984374428, 1935970911, 1889021552, 1843470373, 1799264061, 1756351817, 1714685214, 1674218076, 1634906349, 1596707989, 1559582858, 1523492617, 1488400636, 1454271902, 1421072939, 1388771723, 1357337613, 1326741276, 1296954626, 1267950758, 1239703890, 1212189307, 1185383309, 1159263163, 1133807051, 1108994033, 1084804000, 1061217634, 1038216375, 1015782381, 993898497, 972548222, 951715679, 931385586, 911543232, 892174447, 873265579, 854803472, 836775446, 819169269, 801973146, 785175693, 768765926, 752733236, 737067380, 721758463, 706796921, 692173513, 677879301, 663905642, 650244175, 636886809, 623825713, 611053303, 598562237, 586345402, 574395905, 562707067, 551272411, 540085659, 529140720, 518431686, 507952824, 497698568, 487663518, 477842426, 468230199, 458821887, 449612682, 440597908, 431773025, 423133613, 414675379, 406394144, 398285844, 390346524, 382572336, 374959534, 367504472, 360203597, 353053453, 346050670, 339191967, 332474147, 325894095, 319448773, 313135221]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 871).prefactor = (4610300601438147/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 871).cutoff/(generalMeanRows 871).c)).2 =
    (191766589336141/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 871).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 871).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 871).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 871

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 871).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 871).criticalRate j.val*(generalMeanRows 871).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 871).c*(generalMeanRows 871).criticalPoint j.val)).2-
      (generalMeanRows 871).J/2-(generalMeanRows 871).error (generalMeanGrid j.val)+
      (generalMeanRows 871).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 871).c)).2-
      (generalMeanRows 871).J/2-(generalMeanRows 871).error 4 := by
  have he : (generalMeanRows 871).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 871) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 871)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0871

/-! Kernel-checked entropy margins for general spectral rectangle 872. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0872
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5066782517, 4897769761, 4736143750, 4581489650, 4433421765, 4291580988, 4155632531, 4025263895, 3900183046, 3780116780, 3664809240, 3554020579, 3447525753, 3345113415, 3246584916, 3151753390, 3060442920, 2972487776, 2887731710, 2806027317, 2727235440, 2651224627, 2577870631, 2507055940, 2438669354, 2372605585, 2308764887, 2247052721, 2187379431, 2129659952, 2073813539, 2019763504, 1967436988, 1916764728, 1867680861, 1820122720, 1774030659, 1729347884, 1686020291, 1643996318, 1603226810, 1563664881, 1525265800, 1487986868, 1451787314, 1416628195, 1382472294, 1349284038, 1317029407, 1285675858, 1255192246, 1225548759, 1196716846, 1168669156, 1141379478, 1114822686, 1088974685, 1063812361, 1039313534, 1015456911, 992222049, 969589309, 947539821, 926055449, 905118753, 884712963, 864821943, 845430162, 826522674, 808085080, 790103516, 772564619, 755455510, 738763775, 722477438, 706584948, 691075158, 675937310, 661161015, 646736242, 632653298, 618902819, 605475752, 592363347, 579557140, 567048945, 554830841, 542895162, 531234487, 519841630, 508709632, 497831751, 487201454, 476812409, 466658479, 456733711, 447032334, 437548748, 428277519, 419213376, 410351199, 401686020, 393213014, 384927492, 376824904, 368900823, 361150952, 353571112, 346157238, 338905382, 331811702, 324872460, 318084021, 311442848, 304945498, 298588621, 292368956, 286283325, 280328638, 274501883, 268800126]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 872).prefactor = (4642889775161523/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 872).cutoff/(generalMeanRows 872).c)).2 =
    (92299003881469/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 872).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 872).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 872).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 872

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 872).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 872).criticalRate j.val*(generalMeanRows 872).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 872).c*(generalMeanRows 872).criticalPoint j.val)).2-
      (generalMeanRows 872).J/2-(generalMeanRows 872).error (generalMeanGrid j.val)+
      (generalMeanRows 872).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 872).c)).2-
      (generalMeanRows 872).J/2-(generalMeanRows 872).error 4 := by
  have he : (generalMeanRows 872).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 872) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 872)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0872

/-! Kernel-checked entropy margins for general spectral rectangle 873. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0873
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5027488959, 4857638236, 4695215284, 4539804905, 4391020964, 4248503855, 4111918231, 3980950983, 3855309426, 3734719658, 3618925092, 3507685124, 3400773921, 3297979329, 3199101874, 3103953849, 3012358488, 2924149200, 2839168873, 2757269234, 2678310258, 2602159628, 2528692233, 2457789704, 2389339989, 2323236958, 2259380032, 2197673847, 2138027937, 2080356438, 2024577818, 1970614618, 1918393220, 1867843621, 1818899225, 1771496658, 1725575576, 1681078503, 1637950674, 1596139878, 1555596328, 1516272525, 1478123139, 1441104888, 1405176437, 1370298291, 1336432702, 1303543577, 1271596394, 1240558122, 1210397147, 1181083199, 1152587284, 1124881625, 1097939596, 1071735673, 1046245373, 1021445212, 997312648, 973826043, 950964620, 928708416, 907038253, 885935695, 865383016, 845363168, 825859750, 806856978, 788339658, 770293158, 752703387, 735556766, 718840210, 702541105, 686647286, 671147020, 656028988, 641282263, 626896300, 612860916, 599166274, 585802872, 572761529, 560033368, 547609808, 535482551, 523643569, 512085096, 500799615, 489779850, 479018757, 468509512, 458245509, 448220343, 438427810, 428861896, 419516769, 410386775, 401466430, 392750413, 384233562, 375910868, 367777467, 359828638, 352059797, 344466491, 337044394, 329789304, 322697138, 315763927, 308985812, 302359044, 295879975, 289545057, 283350840, 277293968, 271371176, 265579283, 259915199, 254375911, 248958489]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 873).prefactor = (1163286714841199/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 873).cutoff/(generalMeanRows 873).c)).2 =
    (89178234645377/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 873).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 873).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 873).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 873

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 873).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 873).criticalRate j.val*(generalMeanRows 873).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 873).c*(generalMeanRows 873).criticalPoint j.val)).2-
      (generalMeanRows 873).J/2-(generalMeanRows 873).error (generalMeanGrid j.val)+
      (generalMeanRows 873).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 873).c)).2-
      (generalMeanRows 873).J/2-(generalMeanRows 873).error 4 := by
  have he : (generalMeanRows 873).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 873) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 873)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0873

/-! Kernel-checked entropy margins for general spectral rectangle 874. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0874
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4983796714, 4813212466, 4650118577, 4494096536, 4344757098, 4201737733, 4064700342, 3933329223, 3807329242, 3686424185, 3570355280, 3458879851, 3351770104, 3248812027, 3149804379, 3054557778, 2962893863, 2874644528, 2789651218, 2707764288, 2628842403, 2552751999, 2479366775, 2408567227, 2340240219, 2274278585, 2210580759, 2149050433, 2089596236, 2032131442, 1976573693, 1922844740, 1870870209, 1820579373, 1771904947, 1724782890, 1679152225, 1634954870, 1592135475, 1550641274, 1510421945, 1471429479, 1433618054, 1396943920, 1361365293, 1326842247, 1293336621, 1260811927, 1229233267, 1198567246, 1168781902, 1139846634, 1111732131, 1084410309, 1057854253, 1032038159, 1006937279, 982527871, 958787151, 935693249, 913225161, 891362715, 870086528, 849377970, 829219129, 809592780, 790482355, 771871906, 753746088, 736090122, 718889778, 702131346, 685801615, 669887849, 654377772, 639259543, 624521739, 610153339, 596143705, 582482567, 569160007, 556166446, 543492629, 531129611, 519068748, 507301679, 495820322, 484616856, 473683716, 463013579, 452599358, 442434190, 432511432, 422824646, 413367595, 404134238, 395118718, 386315356, 377718648, 369323254, 361123996, 353115850, 345293939, 337653533, 330190038, 322898994, 315776072, 308817064, 302017886, 295374568, 288883253, 282540193, 276341743, 270284361, 264364604, 258579121, 252924656, 247398038, 241996185, 236716097, 231554855]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 874).prefactor = (4686616926127301/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 874).cutoff/(generalMeanRows 874).c)).2 =
    (174835327978047/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 874).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 874).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 874).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 874

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 874).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 874).criticalRate j.val*(generalMeanRows 874).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 874).c*(generalMeanRows 874).criticalPoint j.val)).2-
      (generalMeanRows 874).J/2-(generalMeanRows 874).error (generalMeanGrid j.val)+
      (generalMeanRows 874).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 874).c)).2-
      (generalMeanRows 874).J/2-(generalMeanRows 874).error 4 := by
  have he : (generalMeanRows 874).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 874) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 874)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0874

/-! Kernel-checked entropy margins for general spectral rectangle 875. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0875
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5237212901, 5070003132, 4909978113, 4756735389, 4609900802, 4469126007, 4334086272, 4204478499, 4080019455, 3960444180, 3845504549, 3734967971, 3628616218, 3526244349, 3427659744, 3332681210, 3241138176, 3152869950, 3067725036, 2985560514, 2906241464, 2829640435, 2755636963, 2684117114, 2614973073, 2548102757, 2483409458, 2420801509, 2360191983, 2301498400, 2244642466, 2189549822, 2136149815, 2084375283, 2034162351, 1985450247, 1938181125, 1892299900, 1847754092, 1804493687, 1762471000, 1721640545, 1681958922, 1643384698, 1605878311, 1569401963, 1533919533, 1499396486, 1465799795, 1433097858, 1401260433, 1370258559, 1340064503, 1310651688, 1281994643, 1254068945, 1226851169, 1200318838, 1174450377, 1149225074, 1124623033, 1100625137, 1077213015, 1054369001, 1032076107, 1010317986, 989078909, 968343730, 948097867, 928327269, 909018398, 890158202, 871734099, 853733950, 836146044, 818959079, 802162143, 785744698, 769696564, 754007907, 738669217, 723671304, 709005277, 694662538, 680634764, 666913900, 653492149, 640361959, 627516013, 614947224, 602648721, 590613843, 578836133, 567309327, 556027347, 544984295, 534174449, 523592251, 513232304, 503089368, 493158349, 483434301, 473912414, 464588013, 455456551, 446513610, 437754887, 429176200, 420773477, 412542756, 404480180, 396581992, 388844536, 381264250, 373837662, 366561394, 359432149, 352446717, 345601967, 338894849, 332322386]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 875).prefactor = (2275929568388031/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 875).cutoff/(generalMeanRows 875).c)).2 =
    (192785286635461/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 875).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 875).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 875).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 875

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 875).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 875).criticalRate j.val*(generalMeanRows 875).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 875).c*(generalMeanRows 875).criticalPoint j.val)).2-
      (generalMeanRows 875).J/2-(generalMeanRows 875).error (generalMeanGrid j.val)+
      (generalMeanRows 875).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 875).c)).2-
      (generalMeanRows 875).J/2-(generalMeanRows 875).error 4 := by
  have he : (generalMeanRows 875).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 875) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 875)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0875

/-! Kernel-checked entropy margins for general spectral rectangle 876. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0876
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5063032718, 4894591015, 4733469564, 4579259295, 4431579807, 4290076862, 4154420151, 4024301295, 3899432054, 3779542711, 3664380623, 3553708900, 3447305219, 3344960738, 3246479111, 3151675595, 3060376222, 2972417053, 2887643491, 2805909642, 2727077740, 2651017609, 2577606170, 2506726984, 2438269831, 2372130321, 2308209530, 2246413664, 2186653752, 2128845351, 2072908280, 2018766365, 1966347209, 1915581974, 1866405172, 1818754479, 1772570556, 1727796883, 1684379598, 1642267360, 1601411202, 1561764410, 1523282397, 1485922594, 1449644340, 1414408784, 1380178788, 1346918843, 1314594981, 1283174698, 1252626882, 1222921738, 1194030727, 1165926502, 1138582849, 1111974632, 1086077739, 1060869036, 1036326317, 1012428260, 989154388, 966485024, 944401261, 922884918, 901918514, 881485230, 861568883, 842153894, 823225266, 804768550, 786769829, 769215688, 752093198, 735389889, 719093735, 703193131, 687676878, 672534167, 657754556, 643327963, 629244646, 615495189, 602070491, 588961753, 576160464, 563658390, 551447565, 539520276, 527869059, 516486684, 505366150, 494500673, 483883680, 473508798, 463369853, 453460853, 443775990, 434309629, 425056302, 416010702, 407167677, 398522227, 390069495, 381804764, 373723452, 365821106, 358093399, 350536126, 343145198, 335916639, 328846585, 321931273, 315167047, 308550346, 302077708, 295745761, 289551224, 283490902, 277561685, 271760543, 266084526]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 876).prefactor = (288580346407003/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 876).cutoff/(generalMeanRows 876).c)).2 =
    (182146587411819/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 876).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 876).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 876).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 876

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 876).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 876).criticalRate j.val*(generalMeanRows 876).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 876).c*(generalMeanRows 876).criticalPoint j.val)).2-
      (generalMeanRows 876).J/2-(generalMeanRows 876).error (generalMeanGrid j.val)+
      (generalMeanRows 876).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 876).c)).2-
      (generalMeanRows 876).J/2-(generalMeanRows 876).error 4 := by
  have he : (generalMeanRows 876).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 876) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 876)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0876

/-! Kernel-checked entropy margins for general spectral rectangle 877. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0877
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5021381644, 4851629298, 4689325581, 4534052433, 4385421122, 4243069688, 4106660659, 3975879003, 3850430298, 3730039080, 3614447356, 3503413257, 3396709820, 3294123880, 3195455060, 3100514853, 3009125782, 2921120630, 2836341735, 2754640345, 2675876019, 2599916079, 2526635109, 2455914480, 2387641926, 2321711139, 2258021400, 2196477238, 2136988106, 2079468086, 2023835617, 1970013230, 1917927317, 1867507899, 1818688426, 1771405573, 1725599064, 1681211500, 1638188198, 1596477042, 1556028342, 1516794704, 1478730905, 1441793778, 1405942102, 1371136502, 1337339348, 1304514668, 1272628063, 1241646623, 1211538857, 1182274614, 1153825022, 1126162423, 1099260310, 1073093274, 1047636948, 1022867960, 998763878, 975303175, 952465177, 930230027, 908578647, 887492701, 866954558, 846947265, 827454511, 808460601, 789950426, 771909439, 754323627, 737179492, 720464022, 704164677, 688269362, 672766413, 657644574, 642892985, 628501159, 614458972, 600756644, 587384728, 574334092, 561595912, 549161654, 537023066, 525172164, 513601224, 502302769, 491269564, 480494598, 469971087, 459692455, 449652332, 439844542, 430263102, 420902208, 411756231, 402819715, 394087361, 385554030, 377214735, 369064633, 361099023, 353313337, 345703141, 338264126, 330992106, 323883012, 316932888, 310137890, 303494279, 296998420, 290646777, 284435909, 278362469, 272423201, 266614934, 260934583, 255379145, 249945695]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 877).prefactor = (2337854657196873/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 877).cutoff/(generalMeanRows 877).c)).2 =
    (707233959407/1953125000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 877).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 877).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 877).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 877

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 877).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 877).criticalRate j.val*(generalMeanRows 877).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 877).c*(generalMeanRows 877).criticalPoint j.val)).2-
      (generalMeanRows 877).J/2-(generalMeanRows 877).error (generalMeanGrid j.val)+
      (generalMeanRows 877).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 877).c)).2-
      (generalMeanRows 877).J/2-(generalMeanRows 877).error 4 := by
  have he : (generalMeanRows 877).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 877) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 877)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0877

/-! Kernel-checked entropy margins for general spectral rectangle 878. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0878
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4976770160, 4806305082, 4643350506, 4487485094, 4338317038, 4195481488, 4058638247, 3927469718, 3801679058, 3680988515, 3565137933, 3453883394, 3346995994, 3244260728, 3145475471, 3050450059, 2959005435, 2870972883, 2786193314, 2704516615, 2625801049, 2549912704, 2476724983, 2406118137, 2337978825, 2272199713, 2208679105, 2147320593, 2088032735, 2030728760, 1975326287, 1921747067, 1869916740, 1819764614, 1771223449, 1724229267, 1678721161, 1634641132, 1591933918, 1550546852, 1510429714, 1471534605, 1433815816, 1397229715, 1361734636, 1327290775, 1293860096, 1261406235, 1229894418, 1199291376, 1169565273, 1140685631, 1112623263, 1085350207, 1058839669, 1033065963, 1008004459, 983631531, 959924507, 936861627, 914421997, 892585550, 871333006, 850645835, 830506226, 810897047, 791801822, 773204696, 755090409, 737444269, 720252126, 703500350, 687175806, 671265835, 655758231, 640641222, 625903453, 611533966, 597522186, 583857901, 570531253, 557532718, 544853092, 532483483, 520415294, 508640214, 497150202, 485937484, 474994533, 464314069, 453889040, 443712621, 433778202, 424079379, 414609948, 405363895, 396335392, 387518790, 378908609, 370499534, 362286411, 354264237, 346428159, 338773464, 331295578, 323990061, 316852599, 309879001, 303065198, 296407236, 289901269, 283543564, 277330487, 271258509, 265324196, 259524207, 253855296, 248314302, 242898149, 237603847, 232428482]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 878).prefactor = (4708760847536567/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 878).cutoff/(generalMeanRows 878).c)).2 =
    (355061504590973/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 878).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 878).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 878).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 878

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 878).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 878).criticalRate j.val*(generalMeanRows 878).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 878).c*(generalMeanRows 878).criticalPoint j.val)).2-
      (generalMeanRows 878).J/2-(generalMeanRows 878).error (generalMeanGrid j.val)+
      (generalMeanRows 878).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 878).c)).2-
      (generalMeanRows 878).J/2-(generalMeanRows 878).error 4 := by
  have he : (generalMeanRows 878).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 878) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 878)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0878

/-! Kernel-checked entropy margins for general spectral rectangle 879. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0879
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4940867383, 4769575391, 4605836322, 4449228307, 4299358948, 4155862752, 4018398832, 3886648859, 3760315218, 3639119355, 3522800284, 3411113235, 3303828431, 3200729977, 3101614849, 3006291971, 2914581373, 2826313418, 2741328097, 2659474378, 2580609609, 2504598968, 2431314956, 2360636926, 2292450653, 2226647932, 2163126203, 2101788209, 2042541676, 1985299011, 1929977029, 1876496692, 1824782868, 1774764110, 1726372440, 1679543156, 1634214650, 1590328235, 1547827981, 1506660569, 1466775147, 1428123198, 1390658416, 1354336587, 1319115481, 1284954749, 1251815822, 1219661823, 1188457482, 1158169048, 1128764220, 1100212069, 1072482973, 1045548552, 1019381607, 993956061, 969246907, 945230155, 921882785, 899182700, 877108682, 855640353, 834758133, 814443206, 794677483, 775443569, 756724733, 738504877, 720768508, 703500709, 686687118, 670313901, 654367727, 638835751, 623705588, 608965297, 594603361, 580608669, 566970498, 553678499, 540722679, 528093389, 515781307, 503777428, 492073048, 480659755, 469529414, 458674159, 448086380, 437758717, 427684045, 417855469, 408266311, 398910108, 389780599, 380871718, 372177588, 363692513, 355410973, 347327615, 339437250, 331734843, 324215512, 316874520, 309707269, 302709298, 295876276, 289203997, 282688380, 276325457, 270111378, 264042400, 258114887, 252325305, 246670221, 241146295, 235750283, 230479027, 225329458, 220298593, 215383525]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 879).prefactor = (2360163871473133/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 879).cutoff/(generalMeanRows 879).c)).2 =
    (2741420963721/8000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 879).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 879).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 879).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 879

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 879).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 879).criticalRate j.val*(generalMeanRows 879).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 879).c*(generalMeanRows 879).criticalPoint j.val)).2-
      (generalMeanRows 879).J/2-(generalMeanRows 879).error (generalMeanGrid j.val)+
      (generalMeanRows 879).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 879).c)).2-
      (generalMeanRows 879).J/2-(generalMeanRows 879).error 4 := by
  have he : (generalMeanRows 879).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 879) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 879)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0879

/-! Kernel-checked entropy margins for general spectral rectangle 880. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0880
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5314873860, 5147534719, 4987407574, 4834084676, 4687187107, 4546362258, 4411281574, 4281638548, 4157146907, 4037538993, 3922564291, 3811988108, 3705590365, 3603164511, 3504516526, 3409464014, 3317835380, 3229469064, 3144212853, 3061923240, 2982464838, 2905709840, 2831537522, 2759833778, 2690490703, 2623406192, 2558483580, 2495631302, 2434762581, 2375795133, 2318650899, 2263255791, 2209539458, 2157435063, 2106879082, 2057811112, 2010173692, 1963912134, 1918974370, 1875310803, 1832874172, 1791619422, 1751503582, 1712485654, 1674526508, 1637588779, 1601636773, 1566636383, 1532555001, 1499361443, 1467025876, 1435519744, 1404815708, 1374887583, 1345710278, 1317259744, 1289512919, 1262447683, 1236042809, 1210277921, 1185133453, 1160590607, 1136631322, 1113238235, 1090394646, 1068084495, 1046292323, 1025003250, 1004202948, 983877613, 964013944, 944599119, 925620775, 907066986, 888926244, 871187444, 853839860, 836873135, 820277262, 804042570, 788159709, 772619639, 757413614, 742533171, 727970120, 713716531, 699764724, 686107258, 672736926, 659646740, 646829924, 634279910, 621990323, 609954981, 598167881, 586623197, 575315272, 564238609, 553387872, 542757871, 532343566, 522140053, 512142567, 502346472, 492747257, 483340533, 474122032, 465087593, 456233171, 447554823, 439048709, 430711091, 422538322, 414526852, 406673220, 398974049, 391426051, 384026015, 376770813, 369657390, 362682767]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 880).prefactor = (4595672824760777/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 880).cutoff/(generalMeanRows 880).c)).2 =
    (403460138021697/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 880).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 880).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 880).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 880

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 880).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 880).criticalRate j.val*(generalMeanRows 880).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 880).c*(generalMeanRows 880).criticalPoint j.val)).2-
      (generalMeanRows 880).J/2-(generalMeanRows 880).error (generalMeanGrid j.val)+
      (generalMeanRows 880).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 880).c)).2-
      (generalMeanRows 880).J/2-(generalMeanRows 880).error 4 := by
  have he : (generalMeanRows 880).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 880) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 880)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0880

/-! Kernel-checked entropy margins for general spectral rectangle 881. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0881
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5216041759, 5047057794, 4885409039, 4730681625, 4582490884, 4440478795, 4304311707, 4173678305, 4048287772, 3927868153, 3812164866, 3700939358, 3593967892, 3491040441, 3391959678, 3296540065, 3204607009, 3115996097, 3030552395, 2948129797, 2868590435, 2791804132, 2717647896, 2646005454, 2576766825, 2509827917, 2445090161, 2382460167, 2321849409, 2263173925, 2206354047, 2151314140, 2097982370, 2046290477, 1996173566, 1947569921, 1900420816, 1854670349, 1810265283, 1767154900, 1725290857, 1684627060, 1645119539, 1606726335, 1569407392, 1533124454, 1497840971, 1463522011, 1430134173, 1397645508, 1366025447, 1335244728, 1305275331, 1276090413, 1247664254, 1219972196, 1192990594, 1166696764, 1141068939, 1116086222, 1091728545, 1067976631, 1044811952, 1022216700, 1000173749, 978666624, 957679472, 937197032, 917204609, 897688050, 878633715, 860028459, 841859607, 824114936, 806782653, 789851375, 773310117, 757148267, 741355578, 725922148, 710838407, 696095100, 681683281, 667594293, 653819761, 640351580, 627181900, 614303121, 601707883, 589389051, 577339714, 565553168, 554022917, 542742658, 531706277, 520907842, 510341593, 500001942, 489883460, 479980874, 470289064, 460803054, 451518006, 442429221, 433532126, 424822277, 416295351, 407947142, 399773557, 391770613, 383934434, 376261246, 368747373, 361389237, 354183351, 347126319, 340214832, 333445665, 326815675, 320321797, 313961046]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 881).prefactor = (291216428595997/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 881).cutoff/(generalMeanRows 881).c)).2 =
    (389122974875291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 881).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 881).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 881).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 881

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 881).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 881).criticalRate j.val*(generalMeanRows 881).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 881).c*(generalMeanRows 881).criticalPoint j.val)).2-
      (generalMeanRows 881).J/2-(generalMeanRows 881).error (generalMeanGrid j.val)+
      (generalMeanRows 881).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 881).c)).2-
      (generalMeanRows 881).J/2-(generalMeanRows 881).error 4 := by
  have he : (generalMeanRows 881).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 881) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 881)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0881

/-! Kernel-checked entropy margins for general spectral rectangle 882. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0882
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4897921680, 4728512760, 4566557532, 4411640008, 4263373269, 4121396924, 3985374847, 3854993159, 3729958406, 3609995930, 3494848393, 3384274447, 3278047531, 3175954765, 3077795964, 2983382719, 2892537570, 2805093246, 2720891965, 2639784795, 2561631065, 2486297821, 2413659327, 2343596602, 2275996994, 2210753784, 2147765815, 2086937160, 2028176799, 1971398327, 1916519684, 1863462894, 1812153833, 1762522005, 1714500336, 1668024979, 1623035134, 1579472880, 1537283017, 1496412911, 1456812365, 1418433479, 1381230533, 1345159870, 1310179786, 1276250431, 1243333711, 1211393199, 1180394049, 1150302915, 1121087879, 1092718377, 1065165131, 1038400088, 1012396359, 987128162, 962570769, 938700457, 915494455, 892930906, 870988819, 849648029, 828889162, 808693595, 789043422, 769921423, 751311032, 733196308, 715561908, 698393055, 681675523, 665395603, 649540087, 634096244, 619051798, 604394912, 590114167, 576198545, 562637412, 549420502, 536537903, 523980041, 511737667, 499801843, 488163932, 476815581, 465748715, 454955524, 444428452, 434160186, 424143651, 414371996, 404838589, 395537005, 386461023, 377604614, 368961937, 360527329, 352295302, 344260534, 336417864, 328762285, 321288941, 313993120, 306870249, 299915888, 293125728, 286495584, 280021395, 273699212, 267525202, 261495639, 255606905, 249855481, 244237948, 238750982, 233391350, 228155910, 223041605, 218045462, 213164589]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 882).prefactor = (1170913089601371/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 882).cutoff/(generalMeanRows 882).c)).2 =
    (171729543960397/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 882).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 882).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 882).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 882

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 882).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 882).criticalRate j.val*(generalMeanRows 882).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 882).c*(generalMeanRows 882).criticalPoint j.val)).2-
      (generalMeanRows 882).J/2-(generalMeanRows 882).error (generalMeanGrid j.val)+
      (generalMeanRows 882).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 882).c)).2-
      (generalMeanRows 882).J/2-(generalMeanRows 882).error 4 := by
  have he : (generalMeanRows 882).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 882) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 882)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0882

/-! Kernel-checked entropy margins for general spectral rectangle 883. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0883
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5258909693, 5092567367, 4933387821, 4780966570, 4634927722, 4494921485, 4360621931, 4231724995, 4107946689, 3989021483, 3874700853, 3764751965, 3658956482, 3557109479, 3459018459, 3364502454, 3273391200, 3185524391, 3100750983, 3018928568, 2939922786, 2863606793, 2789860765, 2718571442, 2649631709, 2582940201, 2518400947, 2455923031, 2395420282, 2336810983, 2280017605, 2224966558, 2171587951, 2119815380, 2069585726, 2020838960, 1973517971, 1927568398, 1882938477, 1839578893, 1797442647, 1756484925, 1716662983, 1677936033, 1640265137, 1603613106, 1567944414, 1533225104, 1499422707, 1466506167, 1434445767, 1403213059, 1372780802, 1343122898, 1314214339, 1286031145, 1258550323, 1231749810, 1205608431, 1180105857, 1155222563, 1130939788, 1107239501, 1084104365, 1061517705, 1039463478, 1017926241, 996891127, 976343816, 956270511, 936657915, 917493208, 898764025, 880458440, 862564939, 845072412, 827970125, 811247714, 794895161, 778902785, 763261226, 747961428, 732994635, 718352369, 704026427, 690008862, 676291982, 662868330, 649730683, 636872037, 624285602, 611964793, 599903221, 588094687, 576533174, 565212840, 554128012, 543273181, 532642994, 522232249, 512035889, 502049000, 492266801, 482684645, 473298007, 464102489, 455093807, 446267793, 437620388, 429147641, 420845702, 412710821, 404739346, 396927716, 389272462, 381770201, 374417637, 367211553, 360148813, 353226359, 346441207]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 883).prefactor = (2294156003676989/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 883).cutoff/(generalMeanRows 883).c)).2 =
    (200425385278717/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 883).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 883).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 883).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 883

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 883).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 883).criticalRate j.val*(generalMeanRows 883).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 883).c*(generalMeanRows 883).criticalPoint j.val)).2-
      (generalMeanRows 883).J/2-(generalMeanRows 883).error (generalMeanGrid j.val)+
      (generalMeanRows 883).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 883).c)).2-
      (generalMeanRows 883).J/2-(generalMeanRows 883).error 4 := by
  have he : (generalMeanRows 883).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 883) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 883)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0883

/-! Kernel-checked entropy margins for general spectral rectangle 884. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0884
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4959426679, 4789852508, 4627756542, 4472717947, 4324345461, 4182274812, 4046166413, 3915703302, 3790589292, 3670547311, 3555317895, 3444657833, 3338338938, 3236146927, 3137880405, 3043349935, 2952377192, 2864794187, 2780442554, 2699172897, 2620844190, 2545323225, 2472484096, 2402207735, 2334381471, 2268898628, 2205658155, 2144564272, 2085526155, 2028457634, 1973276915, 1919906320, 1868272045, 1818303938, 1769935285, 1723102616, 1677745520, 1633806473, 1591230679, 1549965917, 1509962400, 1471172647, 1433551352, 1397055272, 1361643115, 1327275440, 1293914556, 1261524435, 1230070623, 1199520161, 1169841508, 1141004471, 1112980134, 1085740798, 1059259919, 1033512052, 1008472794, 984118738, 960427424, 937377291, 914947636, 893118574, 871870999, 851186547, 831047564, 811437070, 792338730, 773736826, 755616227, 737962362, 720761199, 703999218, 687663388, 671741149, 656220389, 641089424, 626336982, 611952186, 597924533, 584243884, 570900444, 557884753, 545187665, 532800343, 520714241, 508921096, 497412914, 486181960, 475220749, 464522034, 454078802, 443884256, 433931816, 424215105, 414727943, 405464342, 396418494, 387584767, 378957701, 370531997, 362302514, 354264264, 346412404, 338742233, 331249187, 323928831, 316776860, 309789090, 302961456, 296290008, 289770904, 283400414, 277174905, 271090850, 265144815, 259333460, 253653537, 248101885, 242675427, 237371169, 232186197]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 884).prefactor = (4724138325031259/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 884).cutoff/(generalMeanRows 884).c)).2 =
    (180525478048301/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 884).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 884).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 884).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 884

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 884).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 884).criticalRate j.val*(generalMeanRows 884).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 884).c*(generalMeanRows 884).criticalPoint j.val)).2-
      (generalMeanRows 884).J/2-(generalMeanRows 884).error (generalMeanGrid j.val)+
      (generalMeanRows 884).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 884).c)).2-
      (generalMeanRows 884).J/2-(generalMeanRows 884).error 4 := by
  have he : (generalMeanRows 884).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 884) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 884)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0884

/-! Kernel-checked entropy margins for general spectral rectangle 885. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0885
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4949075893, 4777664934, 4613845096, 4457189345, 4307300624, 4163809235, 4026370510, 3894662716, 3768385187, 3647256637, 3531013635, 3419409233, 3312211717, 3209203476, 3110179969, 3014948785, 2923328785, 2835149314, 2750249482, 2668477498, 2589690064, 2513751814, 2440534795, 2369917991, 2301786881, 2236033030, 2172553709, 2111251546, 2052034197, 1994814045, 1939507917, 1886036820, 1834325699, 1784303203, 1735901478, 1689055966, 1643705215, 1599790710, 1557256705, 1516050074, 1476120166, 1437418672, 1399899496, 1363518640, 1328234090, 1294005714, 1260795162, 1228565774, 1197282493, 1166911781, 1137421547, 1108781068, 1080960925, 1053932934, 1027670089, 1002146503, 977337351, 953218821, 929768065, 906963153, 884783028, 863207467, 842217041, 821793076, 801917622, 782573417, 763743856, 745412963, 727565359, 710186240, 693261349, 676776949, 660719808, 645077167, 629836728, 614986631, 600515434, 586412097, 572665965, 559266751, 546204522, 533469683, 521052964, 508945407, 497138353, 485623430, 474392541, 463437854, 452751792, 442327021, 432156444, 422233187, 412550597, 403102226, 393881830, 384883357, 376100942, 367528899, 359161716, 350994048, 343020708, 335236666, 327637040, 320217095, 312972231, 305897984, 298990020, 292244130, 285656223, 279222329, 272938587, 266801248, 260806664, 254951294, 249231691, 243644507, 238186483, 232854450, 227645327, 222556115, 217583897]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 885).prefactor = (598713939685509/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 885).cutoff/(generalMeanRows 885).c)).2 =
    (354154377037541/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 885).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 885).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 885).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 885

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 885).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 885).criticalRate j.val*(generalMeanRows 885).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 885).c*(generalMeanRows 885).criticalPoint j.val)).2-
      (generalMeanRows 885).J/2-(generalMeanRows 885).error (generalMeanGrid j.val)+
      (generalMeanRows 885).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 885).c)).2-
      (generalMeanRows 885).J/2-(generalMeanRows 885).error 4 := by
  have he : (generalMeanRows 885).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 885) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 885)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0885

/-! Kernel-checked entropy margins for general spectral rectangle 886. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0886
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5162086628, 4994153649, 4833505556, 4679731750, 4532450598, 4391306904, 4255969648, 4126129962, 4001499321, 3881807901, 3766803114, 3656248272, 3549921382, 3447614047, 3349130468, 3254286535, 3162908994, 3074834690, 2989909860, 2907989503, 2828936783, 2752622489, 2678924538, 2607727507, 2538922211, 2472405305, 2408078919, 2345850321, 2285631596, 2227339359, 2170894479, 2116221826, 2063250036, 2011911289, 1962141106, 1913878152, 1867064061, 1821643270, 1777562853, 1734772383, 1693223792, 1652871237, 1613670986, 1575581299, 1538562323, 1502575992, 1467585932, 1433557372, 1400457063, 1368253195, 1336915328, 1306414318, 1276722253, 1247812393, 1219659108, 1192237826, 1165524978, 1139497952, 1114135045, 1089415417, 1065319055, 1041826727, 1018919952, 996580957, 974792653, 953538594, 932802955, 912570499, 892826553, 873556979, 854748155, 836386949, 818460696, 800957183, 783864623, 767171639, 750867249, 734940845, 719382181, 704181354, 689328793, 674815244, 660631756, 646769669, 633220605, 619976453, 607029360, 594371721, 581996168, 569895563, 558062986, 546491731, 535175292, 524107361, 513281818, 502692725, 492334316, 482200995, 472287329, 462588040, 453098001, 443812230, 434725886, 425834263, 417132785, 408617004, 400282591, 392125337, 384141146, 376326033, 368676118, 361187623, 353856873, 346680286, 339654375, 332775742, 326041078, 319447157, 312990837, 306669053, 300478819]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 886).prefactor = (4651664009524089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 886).cutoff/(generalMeanRows 886).c)).2 =
    (386766030675697/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 886).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 886).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 886).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 886

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 886).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 886).criticalRate j.val*(generalMeanRows 886).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 886).c*(generalMeanRows 886).criticalPoint j.val)).2-
      (generalMeanRows 886).J/2-(generalMeanRows 886).error (generalMeanGrid j.val)+
      (generalMeanRows 886).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 886).c)).2-
      (generalMeanRows 886).J/2-(generalMeanRows 886).error 4 := by
  have he : (generalMeanRows 886).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 886) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 886)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0886

/-! Kernel-checked entropy margins for general spectral rectangle 887. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0887
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5150074506, 4980228368, 4817778769, 4662309136, 4513432256, 4370787708, 4234039575, 4102874394, 3976999317, 3856140460, 3740041406, 3628461860, 3521176422, 3417973479, 3318654191, 3223031571, 3130929639, 3042182657, 2956634414, 2874137583, 2794553122, 2717749722, 2643603305, 2571996550, 2502818468, 2435963993, 2371333617, 2308833045, 2248372873, 2189868294, 2133238822, 2078408030, 2025303319, 1973855686, 1923999521, 1875672410, 1828814956, 1783370604, 1739285485, 1696508266, 1654990012, 1614684052, 1575545857, 1537532926, 1500604677, 1464722345, 1429848886, 1395948886, 1362988481, 1330935269, 1299758244, 1269427719, 1239915261, 1211193631, 1183236718, 1156019490, 1129517938, 1103709025, 1078570641, 1054081559, 1030221388, 1006970540, 984310187, 962222228, 940689254, 919694516, 899221897, 879255880, 859781522, 840784428, 822250729, 804167056, 786520516, 769298678, 752489545, 736081543, 720063494, 704424609, 689154464, 674242989, 659680449, 645457437, 631564853, 617993897, 604736055, 591783085, 579127011, 566760110, 554674901, 542864138, 531320798, 520038076, 509009374, 498228295, 487688632, 477384367, 467309657, 457458834, 447826394, 438406994, 429195443, 420186702, 411375872, 402758195, 394329045, 386083925, 378018463, 370128408, 362409624, 354858088, 347469887, 340241211, 333168352, 326247702, 319475747, 312849065, 306364325, 300018279, 293807767, 287729707, 281781098]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 887).prefactor = (2357945364528521/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 887).cutoff/(generalMeanRows 887).c)).2 =
    (189898680679801/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 887).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 887).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 887).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 887

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 887).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 887).criticalRate j.val*(generalMeanRows 887).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 887).c*(generalMeanRows 887).criticalPoint j.val)).2-
      (generalMeanRows 887).J/2-(generalMeanRows 887).error (generalMeanGrid j.val)+
      (generalMeanRows 887).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 887).c)).2-
      (generalMeanRows 887).J/2-(generalMeanRows 887).error 4 := by
  have he : (generalMeanRows 887).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 887) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 887)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0887

/-! Kernel-checked entropy margins for general spectral rectangle 888. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0888
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4939112866, 4765873299, 4600338894, 4442076307, 4290682582, 4145782503, 4007026229, 3874087176, 3746660122, 3624459494, 3507217826, 3394684369, 3286623826, 3182815201, 3083050758, 2987135062, 2894884117, 2806124562, 2720692939, 2638435030, 2559205231, 2482865986, 2409287268, 2338346085, 2269926041, 2203916918, 2140214291, 2078719172, 2019337682, 1961980741, 1906563781, 1853006482, 1801232520, 1751169340, 1702747937, 1655902652, 1610570988, 1566693428, 1524213273, 1483076486, 1443231546, 1404629313, 1367222898, 1330967544, 1295820515, 1261740986, 1228689946, 1196630103, 1165525797, 1135342915, 1106048813, 1077612241, 1050003278, 1023193258, 997154716, 971861325, 947287839, 923410048, 900204718, 877649554, 855723150, 834404946, 813675196, 793514921, 773905880, 754830533, 736272011, 718214082, 700641130, 683538117, 666890568, 650684537, 634906591, 619543783, 604583633, 590014109, 575823605, 562000925, 548535265, 535416198, 522633656, 510177918, 498039593, 486209609, 474679197, 463439883, 452483472, 441802043, 431387928, 421233715, 411332227, 401676518, 392259866, 383075759, 374117892, 365380157, 356856636, 348541593, 340429470, 332514877, 324792590, 317257540, 309904813, 302729640, 295727393, 288893582, 282223848, 275713960, 269359810, 263157408, 257102878, 251192456, 245422486, 239789413, 234289784, 228920243, 223677526, 218558460, 213559963, 208679032, 203912752]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 888).prefactor = (4856194895725827/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 888).cutoff/(generalMeanRows 888).c)).2 =
    (10853282349749/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 888).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 888).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 888).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 888

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 888).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 888).criticalRate j.val*(generalMeanRows 888).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 888).c*(generalMeanRows 888).criticalPoint j.val)).2-
      (generalMeanRows 888).J/2-(generalMeanRows 888).error (generalMeanGrid j.val)+
      (generalMeanRows 888).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 888).c)).2-
      (generalMeanRows 888).J/2-(generalMeanRows 888).error 4 := by
  have he : (generalMeanRows 888).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 888) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 888)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0888

/-! Kernel-checked entropy margins for general spectral rectangle 889. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0889
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5299920481, 5129872564, 4967218728, 4811538425, 4662440960, 4519562876, 4382565625, 4251133482, 4124971671, 4003804680, 3887374744, 3775440460, 3667775552, 3564167726, 3464417648, 3368338000, 3275752619, 3186495712, 3100411137, 3017351737, 2937178734, 2859761169, 2784975382, 2712704540, 2642838190, 2575271858, 2509906667, 2446648987, 2385410110, 2326105950, 2268656760, 2212986872, 2159024451, 2106701275, 2055952512, 2006716536, 1958934731, 1912551324, 1867513224, 1823769871, 1781273089, 1739976964, 1699837709, 1660813555, 1622864639, 1585952899, 1550041984, 1515097157, 1481085211, 1447974393, 1415734323, 1384335927, 1353751369, 1323953986, 1294918232, 1266619619, 1239034666, 1212140848, 1185916551, 1160341023, 1135394339, 1111057355, 1087311673, 1064139605, 1041524141, 1019448916, 997898180, 976856770, 956310082, 936244046, 916645104, 897500184, 878796679, 860522427, 842665692, 825215146, 808159847, 791489228, 775193078, 759261528, 743685033, 728454367, 713560599, 698995091, 684749479, 670815664, 657185802, 643852296, 630807780, 618045118, 605557387, 593337875, 581380071, 569677655, 558224495, 547014638, 536042302, 525301870, 514787889, 504495057, 494418221, 484552373, 474892642, 465434292, 456172714, 447103425, 438222064, 429524382, 421006247, 412663633, 404492619, 396489389, 388650221, 380971491, 373449667, 366081306, 358863051, 351791631, 344863853, 338076607, 331426856]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 889).prefactor = (593821485188663/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 889).cutoff/(generalMeanRows 889).c)).2 =
    (40447889245109/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 889).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 889).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 889).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 889

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 889).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 889).criticalRate j.val*(generalMeanRows 889).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 889).c*(generalMeanRows 889).criticalPoint j.val)).2-
      (generalMeanRows 889).J/2-(generalMeanRows 889).error (generalMeanGrid j.val)+
      (generalMeanRows 889).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 889).c)).2-
      (generalMeanRows 889).J/2-(generalMeanRows 889).error 4 := by
  have he : (generalMeanRows 889).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 889) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 889)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0889

/-! Kernel-checked entropy margins for general spectral rectangle 890. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0890
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5057391256, 4886111713, 4722351761, 4565688398, 4415728371, 4272105580, 4134478758, 4002529397, 3875959886, 3754491838, 3637864576, 3525833769, 3418170190, 3314658597, 3215096700, 3119294237, 3027072111, 2938261616, 2852703719, 2770248399, 2690754047, 2614086909, 2540120567, 2468735471, 2399818500, 2333262552, 2268966172, 2206833204, 2146772462, 2088697436, 2032526007, 1978180190, 1925585888, 1874672668, 1825373548, 1777624800, 1731365766, 1686538686, 1643088534, 1600962868, 1560111691, 1520487312, 1482044227, 1444738997, 1408530144, 1373378041, 1339244819, 1306094274, 1273891781, 1242604215, 1212199872, 1182648396, 1153920716, 1125988978, 1098826487, 1072407646, 1046707908, 1021703721, 997372481, 973692487, 950642899, 928203694, 906355632, 885080216, 864359659, 844176853, 824515334, 805359257, 786693365, 768502966, 750773902, 733492533, 716645710, 700220752, 684205430, 668587945, 653356911, 638501336, 624010606, 609874470, 596083025, 582626699, 569496242, 556682709, 544177450, 531972097, 520058553, 508428983, 497075800, 485991660, 475169449, 464602275, 454283461, 444206536, 434365227, 424753451, 415365310, 406195083, 397237219, 388486331, 379937192, 371584727, 363424009, 355450253, 347658811, 340045168, 332604938, 325333857, 318227782, 311282685, 304494648, 297859864, 291374629, 285035340, 278838490, 272780670, 266858559, 261068928, 255408632, 249874608, 244463876]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 890).prefactor = (4781004243400087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 890).cutoff/(generalMeanRows 890).c)).2 =
    (73200807845453/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 890).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 890).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 890).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 890

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 890).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 890).criticalRate j.val*(generalMeanRows 890).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 890).c*(generalMeanRows 890).criticalPoint j.val)).2-
      (generalMeanRows 890).J/2-(generalMeanRows 890).error (generalMeanGrid j.val)+
      (generalMeanRows 890).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 890).c)).2-
      (generalMeanRows 890).J/2-(generalMeanRows 890).error 4 := by
  have he : (generalMeanRows 890).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 890) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 890)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0890

/-! Kernel-checked entropy margins for general spectral rectangle 891. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0891
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5127219956, 4953575512, 4787554485, 4628728030, 4476697467, 4331091639, 4191564568, 4057793348, 3929476260, 3806331071, 3688093507, 3574515861, 3465365744, 3360424939, 3259488366, 3162363133, 3068867673, 2978830949, 2892091732, 2808497930, 2727905980, 2650180278, 2575192664, 2502821936, 2432953410, 2365478507, 2300294371, 2237303516, 2176413500, 2117536618, 2060589616, 2005493432, 1952172947, 1900556755, 1850576949, 1802168922, 1755271178, 1709825158, 1665775079, 1623067774, 1581652554, 1541481071, 1502507192, 1464686880, 1427978082, 1392340624, 1357736116, 1324127853, 1291480732, 1259761171, 1228937026, 1198977526, 1169853196, 1141535797, 1113998266, 1087214654, 1061160073, 1035810646, 1011143459, 987136509, 963768669, 941019641, 918869917, 897300746, 876294095, 855832619, 835899629, 816479059, 797555443, 779113883, 761140030, 743620053, 726540621, 709888879, 693652430, 677819311, 662377978, 647317288, 632626481, 618295164, 604313296, 590671175, 577359423, 564368970, 551691047, 539317172, 527239135, 515448992, 503939053, 492701872, 481730235, 471017158, 460555869, 450339810, 440362619, 430618131, 421100366, 411803523, 402721975, 393850261, 385183082, 376715293, 368441898, 360358046, 352459025, 344740259, 337197300, 329825825, 322621635, 315580645, 308698884, 301972492, 295397714, 288970896, 282688485, 276547022, 270543144, 264673574, 258935124, 253324691, 247839252]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 891).prefactor = (4847016796756901/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 891).cutoff/(generalMeanRows 891).c)).2 =
    (73200807845453/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 891).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 891).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 891).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 891

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 891).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 891).criticalRate j.val*(generalMeanRows 891).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 891).c*(generalMeanRows 891).criticalPoint j.val)).2-
      (generalMeanRows 891).J/2-(generalMeanRows 891).error (generalMeanGrid j.val)+
      (generalMeanRows 891).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 891).c)).2-
      (generalMeanRows 891).J/2-(generalMeanRows 891).error 4 := by
  have he : (generalMeanRows 891).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 891) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 891)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0891

/-! Kernel-checked entropy margins for general spectral rectangle 892. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0892
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5185245005, 5014824874, 4851851564, 4695902416, 4546584734, 4403533159, 4266407331, 4134889800, 4008684140, 3887513264, 3771117893, 3659255179, 3551697452, 3448231083, 3348655448, 3252781990, 3160433349, 3071442576, 2985652413, 2902914623, 2823089383, 2746044720, 2671655996, 2599805423, 2530381628, 2463279240, 2398398511, 2335644966, 2274929077, 2216165958, 2159275086, 2104180037, 2050808244, 1999090767, 1948962083, 1900359885, 1853224901, 1807500718, 1763133620, 1720072439, 1678268412, 1637675046, 1598247998, 1559944954, 1522725521, 1486551123, 1451384908, 1417191650, 1383937672, 1351590757, 1320120081, 1289496133, 1259690654, 1230676573, 1202427943, 1174919891, 1148128560, 1122031061, 1096605426, 1071830561, 1047686208, 1024152901, 1001211929, 978845305, 957035725, 935766540, 915021728, 894785858, 875044073, 855782056, 836986008, 818642627, 800739084, 783263004, 766202442, 749545870, 733282157, 717400549, 701890659, 686742445, 671946201, 657492542, 643372387, 629576951, 616097734, 602926503, 590055288, 577476370, 565182269, 553165736, 541419745, 529937484, 518712346, 507737923, 497007996, 486516531, 476257671, 466225727, 456415176, 446820655, 437436950, 428258998, 419281876, 410500798, 401911113, 393508295, 385287945, 377245780, 369377636, 361679458, 354147301, 346777323, 339565785, 332509046, 325603557, 318845864, 312232601, 305760488, 299426329, 293227009, 287159491]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 892).prefactor = (4799871355074377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 892).cutoff/(generalMeanRows 892).c)).2 =
    (392672286309427/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 892).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 892).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 892).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 892

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 892).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 892).criticalRate j.val*(generalMeanRows 892).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 892).c*(generalMeanRows 892).criticalPoint j.val)).2-
      (generalMeanRows 892).J/2-(generalMeanRows 892).error (generalMeanGrid j.val)+
      (generalMeanRows 892).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 892).c)).2-
      (generalMeanRows 892).J/2-(generalMeanRows 892).error 4 := by
  have he : (generalMeanRows 892).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 892) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 892)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0892

/-! Kernel-checked entropy margins for general spectral rectangle 893. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0893
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5095844083, 4916566980, 4745262326, 4581482045, 4424809479, 4274856649, 4131261811, 3993687263, 3861817389, 3735356888, 3614029179, 3497574961, 3385750908, 3278328479, 3175092838, 3075841871, 2980385281, 2888543770, 2800148275, 2715039284, 2633066188, 2554086701, 2477966312, 2404577789, 2333800713, 2265521051, 2199630760, 2136027416, 2074613875, 2015297951, 1957992126, 1902613270, 1849082385, 1797324367, 1747267782, 1698844656, 1651990282, 1606643035, 1562744201, 1520237820, 1479070532, 1439191437, 1400551966, 1363105753, 1326808520, 1291617966, 1257493667, 1224396976, 1192290933, 1161140178, 1130910872, 1101570618, 1073088392, 1045434470, 1018580370, 992498788, 967163539, 942549507, 918632591, 895389660, 872798501, 850837783, 829487009, 808726485, 788537276, 768901175, 749800669, 731218908, 713139675, 695547357, 678426922, 661763887, 645544300, 629754714, 614382167, 599414158, 584838632, 570643957, 556818909, 543352655, 530234732, 517455041, 505003823, 492871651, 481049413, 469528303, 458299806, 447355687, 436687981, 426288983, 416151234, 406267518, 396630847, 387234454, 378071789, 369136501, 360422444, 351923655, 343634360, 335548960, 327662024, 319968288, 312462645, 305140141, 297995971, 291025469, 284224108, 277587495, 271111361, 264791565, 258624082, 252605004, 246730536, 240996988, 235400775, 229938414, 224606519, 219401799, 214321053, 209361170, 204519122]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 893).prefactor = (1262643420716837/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 893).cutoff/(generalMeanRows 893).c)).2 =
    (345664354990143/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 893).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 893).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 893).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 893

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 893).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 893).criticalRate j.val*(generalMeanRows 893).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 893).c*(generalMeanRows 893).criticalPoint j.val)).2-
      (generalMeanRows 893).J/2-(generalMeanRows 893).error (generalMeanGrid j.val)+
      (generalMeanRows 893).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 893).c)).2-
      (generalMeanRows 893).J/2-(generalMeanRows 893).error 4 := by
  have he : (generalMeanRows 893).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 893) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 893)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0893

/-! Kernel-checked entropy margins for general spectral rectangle 894. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0894
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7392840357, 7185314593, 6985883603, 6794125892, 6609648923, 6432086505, 6261096486, 6096358699, 5937573125, 5784458259, 5636749637, 5494198517, 5356570679, 5223645352, 5095214236, 4971080606, 4851058511, 4734972033, 4622654608, 4513948413, 4408703794, 4306778746, 4208038433, 4112354743, 4019605879, 3929675983, 3842454779, 3757837252, 3675723345, 3596017677, 3518629280, 3443471357, 3370461052, 3299519237, 3230570316, 3163542036, 3098365311, 3034974062, 2973305059, 2913297780, 2854894275, 2798039036, 2742678876, 2688762821, 2636241997, 2585069533, 2535200463, 2486591638, 2439201642, 2392990706, 2347920641, 2303954756, 2261057797, 2219195877, 2178336422, 2138448102, 2099500785, 2061465481, 2024314291, 1988020362, 1952557840, 1917901828, 1884028344, 1850914285, 1818537386, 1786876189, 1755910006, 1725618890, 1695983600, 1666985577, 1638606914, 1610830328, 1583639139, 1557017240, 1530949078, 1505419633, 1480414392, 1455919334, 1431920907, 1408406013, 1385361988, 1362776584, 1340637958, 1318934651, 1297655576, 1276790004, 1256327549, 1236258157, 1216572092, 1197259924, 1178312520, 1159721029, 1141476875, 1123571748, 1105997588, 1088746582, 1071811155, 1055183956, 1038857855, 1022825934, 1007081479, 991617971, 976429085, 961508674, 946850771, 932449580, 918299468, 904394961, 890730742, 877301638, 864102622, 851128804, 838375429, 825837871, 813511630, 801392324, 789475691, 777757581, 766233952, 754900870, 743754501]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 894).prefactor = (4802138754079373/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 894).cutoff/(generalMeanRows 894).c)).2 =
    (326732587323669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 894).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 894).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 894).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 894

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 894).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 894).criticalRate j.val*(generalMeanRows 894).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 894).c*(generalMeanRows 894).criticalPoint j.val)).2-
      (generalMeanRows 894).J/2-(generalMeanRows 894).error (generalMeanGrid j.val)+
      (generalMeanRows 894).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 894).c)).2-
      (generalMeanRows 894).J/2-(generalMeanRows 894).error 4 := by
  have he : (generalMeanRows 894).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 894) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 894)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0894

/-! Kernel-checked entropy margins for general spectral rectangle 895. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0895
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6850608711, 6635085052, 6428153395, 6229369868, 6038320910, 5854620549, 5677907980, 5507845423, 5344116204, 5186423041, 5034486511, 4888043662, 4746846771, 4610662208, 4479269421, 4352460002, 4230036842, 4111813358, 3997612789, 3887267548, 3780618626, 3677515051, 3577813382, 3481377247, 3388076914, 3297788894, 3210395576, 3125784885, 3043849966, 2964488891, 2887604381, 2813103557, 2740897695, 2670902008, 2603035434, 2537220444, 2473382858, 2411451674, 2351358906, 2293039432, 2236430855, 2181473367, 2128109622, 2076284620, 2025945593, 1977041900, 1929524925, 1883347986, 1838466245, 1794836621, 1752417712, 1711169720, 1671054378, 1632034883, 1594075829, 1557143149, 1521204056, 1486226984, 1452181541, 1419038457, 1386769535, 1355347605, 1324746488, 1294940943, 1265906641, 1237620118, 1210058744, 1183200688, 1157024885, 1131511009, 1106639438, 1082391229, 1058748092, 1035692362, 1013206976, 991275450, 969881854, 949010796, 928647393, 908777261, 889386488, 870461622, 851989651, 833957986, 816354447, 799167246, 782384975, 765996589, 749991396, 734359041, 719089495, 704173045, 689600280, 675362082, 661449614, 647854311, 634567872, 621582246, 608889630, 596482453, 584353375, 572495272, 560901236, 549564561, 538478741, 527637458, 517034583, 506664162, 496520415, 486597729, 476890652, 467393887, 458102288, 449010856, 440114732, 431409194, 422889652, 414551642, 406390826, 398402985, 390584016]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 895).prefactor = (1261118671186149/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 895).cutoff/(generalMeanRows 895).c)).2 =
    (64582465109817/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 895).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 895).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 895).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 895

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 895).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 895).criticalRate j.val*(generalMeanRows 895).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 895).c*(generalMeanRows 895).criticalPoint j.val)).2-
      (generalMeanRows 895).J/2-(generalMeanRows 895).error (generalMeanGrid j.val)+
      (generalMeanRows 895).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 895).c)).2-
      (generalMeanRows 895).J/2-(generalMeanRows 895).error 4 := by
  have he : (generalMeanRows 895).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 895) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 895)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0895

/-! Kernel-checked entropy margins for general spectral rectangle 896. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0896
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6728311106, 6520999017, 6321993782, 6130861699, 5947198746, 5770627926, 5600796910, 5437375950, 5280056001, 5128547054, 4982576630, 4841888423, 4706241087, 4575407120, 4449171869, 4327332612, 4209697732, 4096085952, 3986325647, 3880254203, 3777717434, 3678569047, 3582670144, 3489888763, 3400099463, 3313182926, 3229025598, 3147519352, 3068561178, 2992052889, 2917900853, 2846015740, 2776312285, 2708709072, 2643128324, 2579495712, 2517740176, 2457793751, 2399591415, 2343070933, 2288172722, 2234839716, 2183017242, 2132652901, 2083696464, 2036099760, 1989816583, 1944802595, 1901015242, 1858413670, 1816958644, 1776612474, 1737338949, 1699103265, 1661871964, 1625612872, 1590295046, 1555888715, 1522365233, 1489697026, 1457857549, 1426821240, 1396563479, 1367060547, 1338289588, 1310228573, 1282856267, 1256152194, 1230096607, 1204670455, 1179855361, 1155633587, 1131988014, 1108902115, 1086359930, 1064346047, 1042845575, 1021844130, 1001327809, 981283175, 961697239, 942557440, 923851632, 905568063, 887695368, 870222545, 853138950, 836434278, 820098552, 804122110, 788495595, 773209944, 758256374, 743626376, 729311701, 715304356, 701596587, 688180879, 675049942, 662196703, 649614301, 637296080, 625235577, 613426522, 601862825, 590538575, 579448029, 568585610, 557945902, 547523640, 537313709, 527311138, 517511093, 507908877, 498499921, 489279782, 480244139, 471388788, 462709638, 454202710, 445864130]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 896).prefactor = (1233251389090051/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 896).cutoff/(generalMeanRows 896).c)).2 =
    (29092135582301/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 896).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 896).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 896).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 896

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 896).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 896).criticalRate j.val*(generalMeanRows 896).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 896).c*(generalMeanRows 896).criticalPoint j.val)).2-
      (generalMeanRows 896).J/2-(generalMeanRows 896).error (generalMeanGrid j.val)+
      (generalMeanRows 896).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 896).c)).2-
      (generalMeanRows 896).J/2-(generalMeanRows 896).error 4 := by
  have he : (generalMeanRows 896).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 896) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 896)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0896

/-! Kernel-checked entropy margins for general spectral rectangle 897. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0897
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6557158493, 6358921194, 6168680746, 5986014564, 5810529074, 5641857127, 5479655715, 5323603929, 5173401134, 5028765342, 4889431738, 4755151360, 4625689904, 4500826642, 4380353435, 4264073847, 4151802321, 4043363439, 3938591242, 3837328598, 3739426634, 3644744205, 3553147408, 3464509129, 3378708631, 3295631169, 3215167629, 3137214202, 3061672076, 2988447146, 2917449749, 2848594418, 2781799647, 2716987674, 2654084281, 2593018602, 2533722946, 2476132629, 2420185819, 2365823389, 2312988778, 2261627863, 2211688832, 2163122076, 2115880074, 2069917293, 2025190094, 1981656636, 1939276793, 1898012074, 1857825539, 1818681737, 1780546626, 1743387515, 1707173001, 1671872907, 1637458229, 1603901084, 1571174657, 1539253157, 1508111769, 1477726611, 1448074698, 1419133894, 1390882886, 1363301141, 1336368874, 1310067019, 1284377197, 1259281688, 1234763399, 1210805847, 1187393124, 1164509880, 1142141298, 1120273071, 1098891383, 1077982891, 1057534701, 1037534354, 1017969810, 998829426, 980101946, 961776483, 943842506, 926289823, 909108573, 892289211, 875822495, 859699474, 843911480, 828450117, 813307247, 798474984, 783945684, 769711936, 755766554, 742102566, 728713210, 715591926, 702732345, 690128286, 677773749, 665662908, 653790102, 642149835, 630736766, 619545705, 608571608, 597809570, 587254825, 576902737, 566748795, 556788613, 547017925, 537432575, 528028523, 518801833, 509748674, 500865316, 492148125]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 897).prefactor = (961864045992719/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 897).cutoff/(generalMeanRows 897).c)).2 =
    (32126085890703/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 897).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 897).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 897).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 897

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 897).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 897).criticalRate j.val*(generalMeanRows 897).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 897).c*(generalMeanRows 897).criticalPoint j.val)).2-
      (generalMeanRows 897).J/2-(generalMeanRows 897).error (generalMeanGrid j.val)+
      (generalMeanRows 897).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 897).c)).2-
      (generalMeanRows 897).J/2-(generalMeanRows 897).error 4 := by
  have he : (generalMeanRows 897).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 897) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 897)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0897

/-! Kernel-checked entropy margins for general spectral rectangle 898. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0898
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6343712093, 6155121120, 5974197768, 5800531410, 5633739728, 5473466212, 5319377932, 5171163553, 5028531562, 4891208672, 4758938394, 4631479745, 4508606077, 4390104020, 4275772521, 4165421968, 4058873390, 3955957729, 3856515169, 3760394523, 3667452670, 3577554036, 3490570114, 3406379024, 3324865100, 3245918519, 3169434945, 3095315204, 3023464983, 2953794546, 2886218477, 2820655428, 2757027898, 2695262017, 2635287343, 2577036683, 2520445912, 2465453814, 2412001923, 2360034386, 2309497819, 2260341187, 2212515681, 2165974603, 2120673266, 2076568887, 2033620496, 1991788848, 1951036337, 1911326916, 1872626022, 1834900510, 1798118576, 1762249704, 1727264598, 1693135130, 1659834283, 1627336100, 1595615639, 1564648923, 1534412896, 1504885386, 1476045061, 1447871394, 1420344627, 1393445738, 1367156407, 1341458986, 1316336471, 1291772476, 1267751200, 1244257411, 1221276415, 1198794036, 1176796595, 1155270888, 1134204169, 1113584125, 1093398867, 1073636903, 1054287132, 1035338821, 1016781591, 998605407, 980800561, 963357659, 946267611, 929521616, 913111154, 897027972, 881264078, 865811726, 850663410, 835811854, 821250004, 806971018, 792968261, 779235293, 765765868, 752553919, 739593559, 726879072, 714404904, 702165660, 690156099, 678371126, 666805790, 655455276, 644314902, 633380113, 622646480, 612109692, 601765552, 591609978, 581638993, 571848725, 562235402, 552795352, 543524996, 534420844, 525479498]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 898).prefactor = (73070009182951/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 898).cutoff/(generalMeanRows 898).c)).2 =
    (349648018974057/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 898).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 898).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 898).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 898

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 898).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 898).criticalRate j.val*(generalMeanRows 898).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 898).c*(generalMeanRows 898).criticalPoint j.val)).2-
      (generalMeanRows 898).J/2-(generalMeanRows 898).error (generalMeanGrid j.val)+
      (generalMeanRows 898).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 898).c)).2-
      (generalMeanRows 898).J/2-(generalMeanRows 898).error 4 := by
  have he : (generalMeanRows 898).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 898) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 898)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0898

/-! Kernel-checked entropy margins for general spectral rectangle 899. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0899
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5963096729, 5777091743, 5598766129, 5427707530, 5263532000, 5105881498, 4954421658, 4808839802, 4668843165, 4534157293, 4404524610, 4279703125, 4159465251, 4043596752, 3931895772, 3824171953, 3720245640, 3619947137, 3523116045, 3429600635, 3339257290, 3251949976, 3167549764, 3085934384, 3006987815, 2930599903, 2856666011, 2785086684, 2715767356, 2648618055, 2583553147, 2520491087, 2459354190, 2400068416, 2342563170, 2286771114, 2232627993, 2180072467, 2129045959, 2079492510, 2031358640, 1984593225, 1939147371, 1894974305, 1852029265, 1810269401, 1769653681, 1730142800, 1691699094, 1654286466, 1617870303, 1582417411, 1547895945, 1514275343, 1481526271, 1449620561, 1418531161, 1388232079, 1358698338, 1329905930, 1301831768, 1274453651, 1247750218, 1221700916, 1196285960, 1171486304, 1147283602, 1123660186, 1100599029, 1078083723, 1056098450, 1034627956, 1013657532, 993172984, 973160618, 953607215, 934500014, 915826692, 897575346, 879734477, 862292972, 845240089, 828565446, 812258999, 796311036, 780712160, 765453278, 750525589, 735920573, 721629978, 707645815, 693960341, 680566057, 667455693, 654622202, 642058752, 629758717, 617715670, 605923377, 594375787, 583067028, 571991400, 561143368, 550517557, 540108745, 529911862, 519921978, 510134304, 500544183, 491147089, 481938620, 472914495, 464070549, 455402730, 446907097, 438579811, 430417137, 422415439, 414571175, 406880897, 399341245]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 899).prefactor = (2345913484630603/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 899).cutoff/(generalMeanRows 899).c)).2 =
    (166785034503923/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 899).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 899).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 899).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 899

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 899).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 899).criticalRate j.val*(generalMeanRows 899).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 899).c*(generalMeanRows 899).criticalPoint j.val)).2-
      (generalMeanRows 899).J/2-(generalMeanRows 899).error (generalMeanGrid j.val)+
      (generalMeanRows 899).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 899).c)).2-
      (generalMeanRows 899).J/2-(generalMeanRows 899).error 4 := by
  have he : (generalMeanRows 899).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 899) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 899)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0899

/-! Kernel-checked entropy margins for general spectral rectangle 900. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0900
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5558544614, 5376123707, 5201377025, 5033890921, 4873280225, 4719185734, 4571271992, 4429225297, 4292751921, 4161576519, 4035440683, 3914101647, 3797331112, 3684914183, 3576648392, 3472342825, 3371817312, 3274901688, 3181435123, 3091265499, 3004248842, 2920248795, 2839136137, 2760788335, 2685089131, 2611928159, 2541200592, 2472806809, 2406652093, 2342646342, 2280703809, 2220742850, 2162685696, 2106458235, 2051989813, 1999213044, 1948063633, 1898480214, 1850404187, 1803779582, 1758552913, 1714673058, 1672091130, 1630760369, 1590636031, 1551675289, 1513837138, 1477082303, 1441373157, 1406673639, 1372949178, 1340166623, 1308294176, 1277301326, 1247158788, 1217838450, 1189313313, 1161557443, 1134545924, 1108254805, 1082661066, 1057742566, 1033478011, 1009846914, 986829558, 964406966, 942560863, 921273651, 900528377, 880308706, 860598894, 841383766, 822648685, 804379539, 786562710, 769185061, 752233911, 735697019, 719562564, 703819131, 688455692, 673461591, 658826531, 644540557, 630594045, 616977687, 603682480, 590699715, 578020962, 565638064, 553543124, 541728495, 530186772, 518910782, 507893574, 497128415, 486608777, 476328332, 466280947, 456460672, 446861735, 437478539, 428305653, 419337805, 410569878, 401996905, 393614064, 385416671, 377400176, 369560161, 361892331, 354392514, 347056654, 339880809, 332861146, 325993938, 319275560, 312702488, 306271292, 299978634, 293821268]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 900).prefactor = (939538897218537/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 900).cutoff/(generalMeanRows 900).c)).2 =
    (616833803603/1953125000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 900).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 900).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 900).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 900

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 900).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 900).criticalRate j.val*(generalMeanRows 900).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 900).c*(generalMeanRows 900).criticalPoint j.val)).2-
      (generalMeanRows 900).J/2-(generalMeanRows 900).error (generalMeanGrid j.val)+
      (generalMeanRows 900).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 900).c)).2-
      (generalMeanRows 900).J/2-(generalMeanRows 900).error 4 := by
  have he : (generalMeanRows 900).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 900) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 900)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0900

/-! Kernel-checked entropy margins for general spectral rectangle 901. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0901
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5587305000, 5414211374, 5248367998, 5089377300, 4936869366, 4790499515, 4649946138, 4514908767, 4385106341, 4260275659, 4140169972, 4024557721, 3913221390, 3805956470, 3702570508, 3602882247, 3506720843, 3413925139, 3324343007, 3237830745, 3154252517, 3073479839, 2995391111, 2919871173, 2846810908, 2776106863, 2707660904, 2641379894, 2577175393, 2514963382, 2454664004, 2396201319, 2339503084, 2284500539, 2231128212, 2179323737, 2129027680, 2080183380, 2032736796, 1986636368, 1941832882, 1898279349, 1855930883, 1814744594, 1774679487, 1735696357, 1697757706, 1660827649, 1624871840, 1589857386, 1555752785, 1522527848, 1490153641, 1458602421, 1427847577, 1397863580, 1368625928, 1340111096, 1312296494, 1285160419, 1258682016, 1232841241, 1207618816, 1182996202, 1158955561, 1135479727, 1112552171, 1090156981, 1068278824, 1046902929, 1026015058, 1005601486, 985648974, 966144754, 947076501, 928432324, 910200740, 892370659, 874931369, 857872518, 841184102, 824856449, 808880205, 793246320, 777946042, 762970897, 748312682, 733963455, 719915524, 706161436, 692693970, 679506124, 666591112, 653942354, 641553464, 629418250, 617530701, 605884984, 594475433, 583296548, 572342987, 561609559, 551091221, 540783069, 530680339, 520778396, 511072735, 501558970, 492232837, 483090185, 474126976, 465339274, 456723253, 448275183, 439991431, 431868459, 423902820, 416091153, 408430183, 400916718, 393547644]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 901).prefactor = (2267908576396939/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 901).cutoff/(generalMeanRows 901).c)).2 =
    (184146158515231/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 901).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 901).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 901).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 901

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 901).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 901).criticalRate j.val*(generalMeanRows 901).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 901).c*(generalMeanRows 901).criticalPoint j.val)).2-
      (generalMeanRows 901).J/2-(generalMeanRows 901).error (generalMeanGrid j.val)+
      (generalMeanRows 901).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 901).c)).2-
      (generalMeanRows 901).J/2-(generalMeanRows 901).error 4 := by
  have he : (generalMeanRows 901).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 901) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 901)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0901

/-! Kernel-checked entropy margins for general spectral rectangle 902. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0902
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5323006858, 5153392603, 4990968788, 4835339020, 4686134535, 4543011786, 4405650278, 4273750643, 4147032917, 4025234976, 3908111147, 3795430935, 3686977882, 3582548525, 3481951449, 3385006425, 3291543624, 3201402892, 3114433093, 3030491502, 2949443245, 2871160786, 2795523454, 2722417006, 2651733221, 2583369525, 2517228645, 2453218287, 2391250835, 2331243076, 2273115936, 2216794243, 2162206499, 2109284672, 2057963998, 2008182800, 1959882312, 1913006523, 1867502025, 1823317868, 1780405435, 1738718310, 1698212167, 1658844658, 1620575309, 1583365423, 1547177992, 1511977606, 1477730375, 1444403853, 1411966962, 1380389929, 1349644219, 1319702474, 1290538458, 1262126999, 1234443942, 1207466098, 1181171199, 1155537856, 1130545513, 1106174415, 1082405567, 1059220698, 1036602232, 1014533252, 992997475, 971979220, 951463382, 931435408, 911881271, 892787448, 874140898, 855929041, 838139739, 820761275, 803782340, 787192009, 770979731, 755135311, 739648894, 724510954, 709712280, 695243960, 681097373, 667264177, 653736294, 640505906, 627565439, 614907556, 602525148, 590411325, 578559409, 566962923, 555615586, 544511304, 533644165, 523008431, 512598532, 502409059, 492434760, 482670533, 473111422, 463752610, 454589416, 445617288, 436831802, 428228655, 419803659, 411552744, 403471947, 395557411, 387805384, 380212209, 372774329, 365488279, 358350683, 351358252, 344507784, 337796154, 331220321]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 902).prefactor = (1130817635597337/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 902).cutoff/(generalMeanRows 902).c)).2 =
    (364517164073087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 902).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 902).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 902).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 902

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 902).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 902).criticalRate j.val*(generalMeanRows 902).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 902).c*(generalMeanRows 902).criticalPoint j.val)).2-
      (generalMeanRows 902).J/2-(generalMeanRows 902).error (generalMeanGrid j.val)+
      (generalMeanRows 902).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 902).c)).2-
      (generalMeanRows 902).J/2-(generalMeanRows 902).error 4 := by
  have he : (generalMeanRows 902).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 902) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 902)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0902

/-! Kernel-checked entropy margins for general spectral rectangle 903. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0903
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5326484414, 5158943744, 4998529011, 4844843868, 4697519739, 4556213385, 4420604740, 4290394971, 4165304738, 4045072637, 3929453789, 3818218563, 3711151426, 3608049896, 3508723586, 3412993339, 3320690429, 3231655838, 3145739592, 3062800143, 2982703813, 2905324275, 2830542073, 2758244184, 2688323607, 2620678990, 2555214275, 2491838378, 2430464886, 2371011776, 2313401154, 2257559013, 2203415008, 2150902242, 2099957068, 2050518909, 2002530082, 1955935637, 1910683207, 1866722865, 1824006991, 1782490152, 1742128977, 1702882054, 1664709823, 1627574479, 1591439885, 1556271478, 1522036197, 1488702398, 1456239789, 1424619359, 1393813313, 1363795016, 1334538929, 1306020562, 1278216420, 1251103954, 1224661518, 1198868323, 1173704399, 1149150555, 1125188344, 1101800025, 1078968536, 1056677457, 1034910983, 1013653899, 992891548, 972609810, 952795077, 933434231, 914514620, 896024042, 877950720, 860283290, 843010778, 826122586, 809608476, 793458555, 777663258, 762213340, 747099857, 732314158, 717847871, 703692891, 689841372, 676285715, 663018558, 650032769, 637321433, 624877847, 612695513, 600768125, 589089567, 577653903, 566455372, 555488379, 544747492, 534227435, 523923081, 513829449, 503941696, 494255115, 484765129, 475467285, 466357254, 457430820, 448683884, 440112454, 431712645, 423480672, 415412850, 407505591, 399755397, 392158861, 384712662, 377413563, 370258408, 363244120, 356367699]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 903).prefactor = (4504823902291843/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 903).cutoff/(generalMeanRows 903).c)).2 =
    (95545684893603/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 903).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 903).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 903).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 903

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 903).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 903).criticalRate j.val*(generalMeanRows 903).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 903).c*(generalMeanRows 903).criticalPoint j.val)).2-
      (generalMeanRows 903).J/2-(generalMeanRows 903).error (generalMeanGrid j.val)+
      (generalMeanRows 903).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 903).c)).2-
      (generalMeanRows 903).J/2-(generalMeanRows 903).error 4 := by
  have he : (generalMeanRows 903).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 903) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 903)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0903

/-! Kernel-checked entropy margins for general spectral rectangle 904. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0904
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5152948839, 4983995853, 4822308159, 4667482708, 4519144610, 4376944659, 4240557149, 4109677903, 3984022517, 3863324777, 3747335233, 3635819906, 3528559122, 3425346452, 3325987744, 3230300244, 3138111791, 3049260085, 2963592005, 2880962998, 2801236504, 2724283432, 2649981678, 2578215679, 2508875996, 2441858934, 2377066187, 2314404513, 2253785419, 2195124888, 2138343105, 2083364220, 2030116108, 1978530163, 1928541097, 1880086746, 1833107904, 1787548154, 1743353714, 1700473298, 1658857977, 1618461052, 1579237939, 1541146054, 1504144710, 1468195017, 1433259789, 1399303458, 1366291990, 1334192809, 1302974723, 1272607853, 1243063572, 1214314440, 1186334146, 1159097457, 1132580161, 1106759020, 1081611726, 1057116854, 1033253821, 1010002848, 987344919, 965261753, 943735764, 922750029, 902288264, 882334790, 862874508, 843892872, 825375867, 807309984, 789682197, 772479945, 755691111, 739303999, 723307325, 707690189, 692442069, 677552797, 663012551, 648811835, 634941470, 621392580, 608156580, 595225161, 582590286, 570244172, 558179286, 546388331, 534864238, 523600160, 512589459, 501825703, 491302653, 481014261, 470954660, 461118155, 451499225, 442092506, 432892794, 423895034, 415094318, 406485877, 398065080, 389827425, 381768536, 373884161, 366170163, 358622523, 351237327, 344010772, 336939156, 330018876, 323246426, 316618394, 310131456, 303782378, 297568009, 291485280, 285531202]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 904).prefactor = (2285972615512773/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 904).cutoff/(generalMeanRows 904).c)).2 =
    (22547084257407/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 904).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 904).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 904).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 904

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 904).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 904).criticalRate j.val*(generalMeanRows 904).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 904).c*(generalMeanRows 904).criticalPoint j.val)).2-
      (generalMeanRows 904).J/2-(generalMeanRows 904).error (generalMeanGrid j.val)+
      (generalMeanRows 904).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 904).c)).2-
      (generalMeanRows 904).J/2-(generalMeanRows 904).error 4 := by
  have he : (generalMeanRows 904).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 904) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 904)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0904

/-! Kernel-checked entropy margins for general spectral rectangle 905. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0905
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5237190338, 5065724310, 4901581681, 4744359344, 4593682235, 4449200882, 4310589210, 4177542593, 4049776097, 3927022908, 3809032909, 3695571399, 3586417928, 3481365247, 3380218343, 3282793567, 3188917836, 3098427897, 3011169662, 2926997589, 2845774118, 2767369149, 2691659561, 2618528771, 2547866318, 2479567487, 2413532958, 2349668473, 2287884539, 2228096141, 2170222480, 2114186731, 2059915810, 2007340163, 1956393565, 1907012939, 1859138174, 1812711968, 1767679672, 1723989146, 1681590628, 1640436605, 1600481693, 1561682530, 1523997666, 1487387468, 1451814026, 1417241065, 1383633863, 1350959173, 1319185148, 1288281276, 1258218312, 1228968214, 1200504088, 1172800134, 1145831588, 1119574680, 1094006581, 1069105363, 1044849954, 1021220102, 998196334, 975759922, 953892850, 932577778, 911798018, 891537501, 871780747, 852512846, 833719427, 815386639, 797501126, 780050004, 763020846, 746401660, 730180868, 714347295, 698890145, 683798991, 669063758, 654674707, 640622425, 626897808, 613492050, 600396635, 587603318, 575104122, 562891322, 550957438, 539295224, 527897664, 516757954, 505869503, 495225920, 484821009, 474648760, 464703342, 454979100, 445470544, 436172346, 427079334, 418186484, 409488918, 400981898, 392660819, 384521208, 376558717, 368769118, 361148303, 353692274, 346397145, 339259136, 332274566, 325439859, 318751528, 312206185, 305800529, 299531344, 293395502, 287389954]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 905).prefactor = (229660806242047/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 905).cutoff/(generalMeanRows 905).c)).2 =
    (350282048251219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 905).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 905).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 905).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 905

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 905).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 905).criticalRate j.val*(generalMeanRows 905).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 905).c*(generalMeanRows 905).criticalPoint j.val)).2-
      (generalMeanRows 905).J/2-(generalMeanRows 905).error (generalMeanGrid j.val)+
      (generalMeanRows 905).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 905).c)).2-
      (generalMeanRows 905).J/2-(generalMeanRows 905).error 4 := by
  have he : (generalMeanRows 905).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 905) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 905)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0905

/-! Kernel-checked entropy margins for general spectral rectangle 906. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0906
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5359284685, 5192299536, 5032389032, 4879159599, 4732245269, 4591305260, 4456021824, 4326098317, 4201257472, 4081239843, 3965802410, 3854717302, 3747770660, 3644761588, 3545501208, 3449811797, 3357525994, 3268486079, 3182543313, 3099557327, 3019395563, 2941932762, 2867050487, 2794636684, 2724585279, 2656795801, 2591173034, 2527626695, 2466071137, 2406425066, 2348611285, 2292556450, 2238190849, 2185448188, 2134265396, 2084582445, 2036342175, 1989490135, 1943974433, 1899745595, 1856756434, 1814961926, 1774319093, 1734786896, 1696326130, 1658899328, 1622470674, 1587005911, 1552472269, 1518838381, 1486074217, 1454151016, 1423041220, 1392718418, 1363157286, 1334333536, 1306223865, 1278805904, 1252058181, 1225960069, 1200491752, 1175634185, 1151369058, 1127678761, 1104546351, 1081955526, 1059890589, 1038336426, 1017278477, 996702711, 976595605, 956944119, 937735675, 918958140, 900599801, 882649353, 865095878, 847928830, 831138016, 814713587, 798646021, 782926107, 767544935, 752493884, 737764610, 723349033, 709239328, 695427917, 681907455, 668670822, 655711119, 643021653, 630595934, 618427662, 606510727, 594839197, 583407310, 572209475, 561240257, 550494376, 539966704, 529652253, 519546175, 509643755, 499940408, 490431673, 481113208, 471980789, 463030304, 454257749, 445659224, 437230933, 428969175, 420870347, 412930935, 405147517, 397516755, 390035395, 382700264, 375508267, 368456386]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 906).prefactor = (4503505231216009/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 906).cutoff/(generalMeanRows 906).c)).2 =
    (193457414564233/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 906).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 906).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 906).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 906

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 906).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 906).criticalRate j.val*(generalMeanRows 906).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 906).c*(generalMeanRows 906).criticalPoint j.val)).2-
      (generalMeanRows 906).J/2-(generalMeanRows 906).error (generalMeanGrid j.val)+
      (generalMeanRows 906).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 906).c)).2-
      (generalMeanRows 906).J/2-(generalMeanRows 906).error 4 := by
  have he : (generalMeanRows 906).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 906) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 906)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0906

/-! Kernel-checked entropy margins for general spectral rectangle 907. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0907
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4988433581, 4818338719, 4655646822, 4499947833, 4350860252, 4208028637, 4071121388, 3939828752, 3813861041, 3692947032, 3576832517, 3465278997, 3358062499, 3254972502, 3155810955, 3060391388, 2968538096, 2880085392, 2794876926, 2712765055, 2633610266, 2557280644, 2483651383, 2412604331, 2344027572, 2277815039, 2213866151, 2152085486, 2092382461, 2034671056, 1978869535, 1924900201, 1872689164, 1822166121, 1773264151, 1725919532, 1680071555, 1635662364, 1592636796, 1550942237, 1510528484, 1471347619, 1433353882, 1396503565, 1360754900, 1326067961, 1292404566, 1259728194, 1228003896, 1197198217, 1167279123, 1138215929, 1109979234, 1082540856, 1055873775, 1029952077, 1004750899, 980246380, 956415614, 933236606, 910688226, 888750174, 867402937, 846627756, 826406590, 806722084, 787557539, 768896884, 750724641, 733025911, 715786335, 698992083, 682629822, 666686700, 651150321, 636008732, 621250397, 606864185, 592839351, 579165520, 565832672, 552831129, 540151536, 527784857, 515722352, 503955573, 492476349, 481276776, 470349205, 459686236, 449280703, 439125669, 429214418, 419540441, 410097436, 400879294, 391880094, 383094099, 374515744, 366139633, 357960532, 349973364, 342173203, 334555267, 327114916, 319847646, 312749082, 305814975, 299041201, 292423750, 285958729, 279642353, 273470944, 267440927, 261548826, 255791262, 250164947, 244666686, 239293368, 234041969, 228909546]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 907).prefactor = (580008332425129/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 907).cutoff/(generalMeanRows 907).c)).2 =
    (169886778824659/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 907).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 907).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 907).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 907

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 907).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 907).criticalRate j.val*(generalMeanRows 907).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 907).c*(generalMeanRows 907).criticalPoint j.val)).2-
      (generalMeanRows 907).J/2-(generalMeanRows 907).error (generalMeanGrid j.val)+
      (generalMeanRows 907).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 907).c)).2-
      (generalMeanRows 907).J/2-(generalMeanRows 907).error 4 := by
  have he : (generalMeanRows 907).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 907) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 907)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0907

/-! Kernel-checked entropy margins for general spectral rectangle 908. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0908
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5268387345, 5101791167, 4942323697, 4789585612, 4643205687, 4502838343, 4368161447, 4238874355, 4114696151, 3995364060, 3880632027, 3770269420, 3664059864, 3561800178, 3463299405, 3368377936, 3276866701, 3188606432, 3103446988, 3021246736, 2941871979, 2865196431, 2791100731, 2719472000, 2650203424, 2583193873, 2518347544, 2455573635, 2394786039, 2335903059, 2278847144, 2223544643, 2169925579, 2117923430, 2067474933, 2018519896, 1971001027, 1924863766, 1880056135, 1836528596, 1794233916, 1753127040, 1713164976, 1674306683, 1636512966, 1599746379, 1563971134, 1529153014, 1495259291, 1462258650, 1430121117, 1398817991, 1368321777, 1338606133, 1309645803, 1281416572, 1253895208, 1227059421, 1200887809, 1175359825, 1150455727, 1126156547, 1102444049, 1079300700, 1056709631, 1034654613, 1013120022, 992090816, 971552505, 951491128, 931893229, 912745836, 894036435, 875752957, 857883752, 840417575, 823343569, 806651243, 790330464, 774371436, 758764692, 743501071, 728571718, 713968058, 699681796, 685704901, 672029592, 658648335, 645553829, 632738998, 620196983, 607921130, 595904988, 584142298, 572626985, 561353153, 550315077, 539507198, 528924117, 518560588, 508411512, 498471935, 488737040, 479202141, 469862684, 460714236, 451752485, 442973235, 434372401, 425946006, 417690178, 409601147, 401675238, 393908873, 386298565, 378840916, 371532612, 364370425, 357351205, 350471882, 343729461]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 908).prefactor = (284214854227573/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 908).cutoff/(generalMeanRows 908).c)).2 =
    (390268661226897/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 908).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 908).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 908).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 908

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 908).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 908).criticalRate j.val*(generalMeanRows 908).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 908).c*(generalMeanRows 908).criticalPoint j.val)).2-
      (generalMeanRows 908).J/2-(generalMeanRows 908).error (generalMeanGrid j.val)+
      (generalMeanRows 908).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 908).c)).2-
      (generalMeanRows 908).J/2-(generalMeanRows 908).error 4 := by
  have he : (generalMeanRows 908).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 908) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 908)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0908

/-! Kernel-checked entropy margins for general spectral rectangle 909. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0909
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5185056578, 5016623928, 4855405458, 4701000943, 4553038141, 4411170345, 4275074203, 4144447760, 4019008714, 3898492838, 3782652563, 3671255694, 3564084250, 3460933406, 3361610535, 3265934331, 3173734011, 3084848583, 2999126174, 2916423414, 2836604873, 2759542534, 2685115316, 2613208630, 2543713966, 2476528514, 2411554811, 2348700416, 2287877604, 2229003084, 2171997739, 2116786378, 2063297509, 2011463127, 1961218513, 1912502053, 1865255057, 1819421604, 1774948382, 1731784554, 1689881615, 1649193275, 1609675333, 1571285574, 1533983659, 1497731029, 1462490814, 1428227744, 1394908071, 1362499486, 1330971053, 1300293136, 1270437338, 1241376435, 1213084323, 1185535964, 1158707329, 1132575356, 1107117899, 1082313689, 1058142290, 1034584058, 1011620111, 989232286, 967403111, 946115774, 925354090, 905102473, 885345912, 866069945, 847260632, 828904536, 810988696, 793500613, 776428225, 759759891, 743484372, 727590814, 712068733, 696907999, 682098822, 667631735, 653497587, 639687525, 626192982, 613005670, 600117566, 587520900, 575208149, 563172025, 551405465, 539901626, 528653872, 517655772, 506901087, 496383764, 486097933, 476037894, 466198118, 456573233, 447158025, 437947430, 428936527, 420120536, 411494811, 403054835, 394796219, 386714692, 378806104, 371066415, 363491697, 356078125, 348821979, 341719637, 334767573, 327962353, 321300635, 314779162, 308394761, 302144342, 296024894]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 909).prefactor = (4570279016549309/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 909).cutoff/(generalMeanRows 909).c)).2 =
    (182856310738931/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 909).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 909).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 909).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 909

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 909).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 909).criticalRate j.val*(generalMeanRows 909).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 909).c*(generalMeanRows 909).criticalPoint j.val)).2-
      (generalMeanRows 909).J/2-(generalMeanRows 909).error (generalMeanGrid j.val)+
      (generalMeanRows 909).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 909).c)).2-
      (generalMeanRows 909).J/2-(generalMeanRows 909).error 4 := by
  have he : (generalMeanRows 909).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 909) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 909)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0909

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock12 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 12 i) := by
  fin_cases i
  · exact EntropyRow0840.numerical
  · exact EntropyRow0841.numerical
  · exact EntropyRow0842.numerical
  · exact EntropyRow0843.numerical
  · exact EntropyRow0844.numerical
  · exact EntropyRow0845.numerical
  · exact EntropyRow0846.numerical
  · exact EntropyRow0847.numerical
  · exact EntropyRow0848.numerical
  · exact EntropyRow0849.numerical
  · exact EntropyRow0850.numerical
  · exact EntropyRow0851.numerical
  · exact EntropyRow0852.numerical
  · exact EntropyRow0853.numerical
  · exact EntropyRow0854.numerical
  · exact EntropyRow0855.numerical
  · exact EntropyRow0856.numerical
  · exact EntropyRow0857.numerical
  · exact EntropyRow0858.numerical
  · exact EntropyRow0859.numerical
  · exact EntropyRow0860.numerical
  · exact EntropyRow0861.numerical
  · exact EntropyRow0862.numerical
  · exact EntropyRow0863.numerical
  · exact EntropyRow0864.numerical
  · exact EntropyRow0865.numerical
  · exact EntropyRow0866.numerical
  · exact EntropyRow0867.numerical
  · exact EntropyRow0868.numerical
  · exact EntropyRow0869.numerical
  · exact EntropyRow0870.numerical
  · exact EntropyRow0871.numerical
  · exact EntropyRow0872.numerical
  · exact EntropyRow0873.numerical
  · exact EntropyRow0874.numerical
  · exact EntropyRow0875.numerical
  · exact EntropyRow0876.numerical
  · exact EntropyRow0877.numerical
  · exact EntropyRow0878.numerical
  · exact EntropyRow0879.numerical
  · exact EntropyRow0880.numerical
  · exact EntropyRow0881.numerical
  · exact EntropyRow0882.numerical
  · exact EntropyRow0883.numerical
  · exact EntropyRow0884.numerical
  · exact EntropyRow0885.numerical
  · exact EntropyRow0886.numerical
  · exact EntropyRow0887.numerical
  · exact EntropyRow0888.numerical
  · exact EntropyRow0889.numerical
  · exact EntropyRow0890.numerical
  · exact EntropyRow0891.numerical
  · exact EntropyRow0892.numerical
  · exact EntropyRow0893.numerical
  · exact EntropyRow0894.numerical
  · exact EntropyRow0895.numerical
  · exact EntropyRow0896.numerical
  · exact EntropyRow0897.numerical
  · exact EntropyRow0898.numerical
  · exact EntropyRow0899.numerical
  · exact EntropyRow0900.numerical
  · exact EntropyRow0901.numerical
  · exact EntropyRow0902.numerical
  · exact EntropyRow0903.numerical
  · exact EntropyRow0904.numerical
  · exact EntropyRow0905.numerical
  · exact EntropyRow0906.numerical
  · exact EntropyRow0907.numerical
  · exact EntropyRow0908.numerical
  · exact EntropyRow0909.numerical
end SingularValueBounds.KL.Certificates
