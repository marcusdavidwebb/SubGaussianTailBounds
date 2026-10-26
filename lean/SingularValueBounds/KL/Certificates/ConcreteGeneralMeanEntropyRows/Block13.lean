import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 910. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0910
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5019749163, 4850139030, 4687881035, 4532567992, 4383821095, 4241287441, 4104637821, 3973564736, 3847780629, 3727016291, 3611019418, 3499553317, 3392395725, 3289337744, 3190182860, 3094746066, 3002853043, 2914339425, 2829050114, 2746838659, 2667566680, 2591103342, 2517324864, 2446114070, 2377359975, 2310957394, 2246806590, 2184812940, 2124886627, 2066942354, 2010899079, 1956679761, 1904211137, 1853423498, 1804250492, 1756628935, 1710498632, 1665802212, 1622484978, 1580494757, 1539781763, 1500298476, 1461999515, 1424841529, 1388783092, 1353784598, 1319808175, 1286817589, 1254778166, 1223656713, 1193421441, 1164041899, 1135488904, 1107734485, 1080751817, 1054515170, 1028999857, 1004182181, 980039392, 956549638, 933691929, 911446090, 889792729, 868713200, 848189567, 828204573, 808741611, 789784692, 771318422, 753327970, 735799048, 718717886, 702071209, 685846218, 670030565, 654612338, 639580044, 624922586, 610629250, 596689690, 583093910, 569832254, 556895386, 544274285, 531960225, 519944767, 508219749, 496777271, 485609689, 474709603, 464069847, 453683481, 443543783, 433644241, 423978544, 414540573, 405324399, 396324270, 387534610, 378950007, 370565214, 362375137, 354374832, 346559500, 338924481, 331465251, 324177416, 317056706, 310098973, 303300187, 296656432, 290163899, 283818887, 277617797, 271557128, 265633476, 259843530, 254184068, 248651954, 243244138, 237957652]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 910).prefactor = (4638042861442621/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 910).cutoff/(generalMeanRows 910).c)).2 =
    (344950630029433/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 910).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 910).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 910).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 910

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 910).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 910).criticalRate j.val*(generalMeanRows 910).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 910).c*(generalMeanRows 910).criticalPoint j.val)).2-
      (generalMeanRows 910).J/2-(generalMeanRows 910).error (generalMeanGrid j.val)+
      (generalMeanRows 910).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 910).c)).2-
      (generalMeanRows 910).J/2-(generalMeanRows 910).error 4 := by
  have he : (generalMeanRows 910).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 910) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 910)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0910

/-! Kernel-checked entropy margins for general spectral rectangle 911. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0911
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5175259748, 5006993771, 4845981380, 4691816991, 4544123505, 4402549811, 4266768567, 4136474214, 4011381195, 3891222345, 3775747452, 3664721946, 3557925713, 3455152024, 3356206550, 3260906472, 3169079666, 3080563952, 2995206416, 2912862777, 2833396811, 2756679817, 2682590130, 2611012663, 2541838492, 2474964466, 2410292850, 2347730989, 2287190999, 2228589482, 2171847255, 2116889101, 2063643541, 2012042611, 1962021664, 1913519179, 1866476586, 1820838100, 1776550564, 1733563308, 1691828011, 1651298572, 1611930992, 1573683265, 1536515264, 1500388651, 1465266779, 1431114602, 1397898597, 1365586686, 1334148159, 1303553606, 1273774854, 1244784906, 1216557877, 1189068946, 1162294302, 1136211092, 1110797380, 1086032099, 1061895013, 1038366674, 1015428390, 993062185, 971250769, 949977504, 929226378, 908981972, 889229438, 869954470, 851143279, 832782577, 814859547, 797361825, 780277484, 763595011, 747303292, 731391592, 715849542, 700667123, 685834652, 671342767, 657182412, 643344830, 629821546, 616604359, 603685329, 591056768, 578711227, 566641493, 554840573, 543301691, 532018277, 520983958, 510192555, 499638072, 489314689, 479216759, 469338800, 459675486, 450221647, 440972259, 431922440, 423067448, 414402671, 405923627, 397625956, 389505419, 381557891, 373779361, 366165924, 358713780, 351419230, 344278672, 337288599, 330445597, 323746339, 317187584, 310766173, 304479031, 298323159]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 911).prefactor = (2306233777064153/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 911).cutoff/(generalMeanRows 911).c)).2 =
    (188091960672579/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 911).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 911).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 911).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 911

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 911).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 911).criticalRate j.val*(generalMeanRows 911).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 911).c*(generalMeanRows 911).criticalPoint j.val)).2-
      (generalMeanRows 911).J/2-(generalMeanRows 911).error (generalMeanGrid j.val)+
      (generalMeanRows 911).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 911).c)).2-
      (generalMeanRows 911).J/2-(generalMeanRows 911).error 4 := by
  have he : (generalMeanRows 911).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 911) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 911)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0911

/-! Kernel-checked entropy margins for general spectral rectangle 912. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0912
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5085226817, 4915401284, 4752954459, 4597474316, 4448577698, 4305907802, 4169131924, 4037939448, 3912040039, 3791162020, 3675050906, 3563468079, 3456189589, 3353005064, 3253716714, 3158138434, 3066094968, 2977421161, 2891961260, 2809568279, 2730103415, 2653435506, 2579440535, 2508001172, 2439006346, 2372350856, 2307935004, 2245664258, 2185448939, 2127203928, 2070848395, 2016305547, 1963502390, 1912369513, 1862840881, 1814853639, 1768347943, 1723266780, 1679555821, 1637163269, 1596039719, 1556138035, 1517413224, 1479822321, 1443324285, 1407879897, 1373451666, 1340003736, 1307501808, 1275913054, 1245206051, 1215350701, 1186318172, 1158080834, 1130612196, 1103886854, 1077880440, 1052569565, 1027931781, 1003945529, 980590100, 957845597, 935692893, 914113599, 893090026, 872605159, 852642622, 833186647, 814222055, 795734220, 777709053, 760132973, 742992886, 726276165, 709970631, 694064529, 678546517, 663405642, 648631328, 634213358, 620141861, 606407297, 593000442, 579912378, 567134479, 554658399, 542476064, 530579656, 518961607, 507614589, 496531504, 485705474, 475129834, 464798126, 454704086, 444841642, 435204905, 425788161, 416585866, 407592639, 398803259, 390212654, 381815902, 373608221, 365584965, 357741620, 350073802, 342577247, 335247811, 328081466, 321074293, 314222483, 307522328, 300970223, 294562659, 288296221, 282167585, 276173517, 270310865, 264576563, 258967623]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 912).prefactor = (4678427389840833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 912).cutoff/(generalMeanRows 912).c)).2 =
    (362294809184491/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 912).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 912).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 912).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 912

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 912).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 912).criticalRate j.val*(generalMeanRows 912).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 912).c*(generalMeanRows 912).criticalPoint j.val)).2-
      (generalMeanRows 912).J/2-(generalMeanRows 912).error (generalMeanGrid j.val)+
      (generalMeanRows 912).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 912).c)).2-
      (generalMeanRows 912).J/2-(generalMeanRows 912).error 4 := by
  have he : (generalMeanRows 912).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 912) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 912)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0912

/-! Kernel-checked entropy margins for general spectral rectangle 913. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0913
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4938437334, 4767342862, 4603727906, 4447178449, 4297309276, 4153761457, 4016200111, 3884312395, 3757805709, 3636406079, 3519856701, 3407916618, 3300359532, 3196972715, 3097556025, 3001921008, 2909890069, 2821295730, 2735979932, 2653793405, 2574595086, 2498251582, 2424636676, 2353630868, 2285120957, 2218999642, 2155165169, 2093520987, 2033975437, 1976441463, 1920836343, 1867081430, 1815101925, 1764826651, 1716187854, 1669121004, 1623564624, 1579460116, 1536751605, 1495385796, 1455311828, 1416481151, 1378847400, 1342366284, 1306995472, 1272694501, 1239424671, 1207148961, 1175831944, 1145439704, 1115939763, 1087301011, 1059493635, 1032489060, 1006259888, 980779839, 956023699, 931967272, 908587328, 885861559, 863768539, 842287679, 821399190, 801084048, 781323959, 762101323, 743399208, 725201315, 707491956, 690256019, 673478953, 657146734, 641245850, 625763274, 610686445, 596003249, 581701999, 567771420, 554200627, 540979113, 528096733, 515543687, 503310508, 491388048, 479767466, 468440216, 457398033, 446632925, 436137159, 425903256, 415923975, 406192309, 396701475, 387444904, 378416232, 369609297, 361018128, 352636937, 344460117, 336482229, 328698002, 321102324, 313690236, 306456926, 299397729, 292508114, 285783686, 279220177, 272813444, 266559465, 260454331, 254494249, 248675531, 242994596, 237447963, 232032249, 226744166, 221580518, 216538196, 211614180, 206805531]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 913).prefactor = (4706811445577917/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 913).cutoff/(generalMeanRows 913).c)).2 =
    (66268995594731/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 913).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 913).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 913).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 913

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 913).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 913).criticalRate j.val*(generalMeanRows 913).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 913).c*(generalMeanRows 913).criticalPoint j.val)).2-
      (generalMeanRows 913).J/2-(generalMeanRows 913).error (generalMeanGrid j.val)+
      (generalMeanRows 913).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 913).c)).2-
      (generalMeanRows 913).J/2-(generalMeanRows 913).error 4 := by
  have he : (generalMeanRows 913).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 913) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 913)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0913

/-! Kernel-checked entropy margins for general spectral rectangle 914. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0914
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5246772855, 5079085000, 4918582031, 4764861884, 4617550785, 4476300771, 4340787482, 4210708191, 4085780025, 3965738375, 3850335461, 3739339026, 3632531163, 3529707245, 3430674950, 3335253373, 3243272217, 3154571053, 3068998633, 2986412272, 2906677271, 2829666389, 2755259355, 2683342418, 2613807930, 2546553963, 2481483950, 2418506355, 2357534367, 2298485610, 2241281884, 2185848910, 2132116106, 2080016368, 2029485871, 1980463882, 1932892582, 1886716905, 1841884384, 1798345005, 1756051077, 1714957099, 1675019648, 1636197266, 1598450350, 1561741063, 1526033234, 1491292275, 1457485098, 1424580039, 1392546782, 1361356298, 1330980770, 1301393543, 1272569059, 1244482807, 1217111268, 1190431872, 1164422947, 1139063681, 1114334075, 1090214910, 1066687709, 1043734699, 1021338784, 999483509, 978153034, 957332104, 937006022, 917160628, 897782271, 878857787, 860374481, 842320103, 824682829, 807451246, 790614329, 774161431, 758082262, 742366877, 727005658, 711989308, 697308828, 682955513, 668920937, 655196941, 641775624, 628649334, 615810653, 603252394, 590967589, 578949482, 567191520, 555687345, 544430788, 533415860, 522636748, 512087809, 501763558, 491658670, 481767970, 472086428, 462609155, 453331396, 444248529, 435356058, 426649609, 418124924, 409777862, 401604390, 393600584, 385762620, 378086778, 370569430, 363207044, 355996180, 348933482, 342015682, 335239594, 328602109, 322100200]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 914).prefactor = (1151324973290739/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 914).cutoff/(generalMeanRows 914).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 914).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 914).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 914).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 914

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 914).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 914).criticalRate j.val*(generalMeanRows 914).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 914).c*(generalMeanRows 914).criticalPoint j.val)).2-
      (generalMeanRows 914).J/2-(generalMeanRows 914).error (generalMeanGrid j.val)+
      (generalMeanRows 914).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 914).c)).2-
      (generalMeanRows 914).J/2-(generalMeanRows 914).error 4 := by
  have he : (generalMeanRows 914).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 914) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 914)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0914

/-! Kernel-checked entropy margins for general spectral rectangle 915. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0915
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4920712812, 4749958513, 4586717100, 4430569519, 4281125994, 4138023471, 4000923341, 3869509398, 3743486015, 3622576493, 3506521584, 3395078143, 3288017918, 3185126439, 3086202020, 2991054838, 2899506096, 2811387259, 2726539349, 2644812300, 2566064367, 2490161574, 2416977217, 2346391394, 2278290574, 2212567202, 2149119326, 2087850257, 2028668250, 1971486206, 1916221402, 1862795227, 1811132949, 1761163489, 1712819214, 1666035742, 1620751759, 1576908848, 1534451334, 1493326126, 1453482588, 1414872396, 1377449422, 1341169616, 1305990897, 1271873047, 1238777621, 1206667851, 1175508563, 1145266095, 1115908221, 1087404080, 1059724109, 1032839978, 1006724529, 981351722, 956696578, 932735131, 909444375, 886802226, 864787471, 843379734, 822559433, 802307744, 782606568, 763438497, 744786782, 726635306, 708968554, 691771585, 675030010, 658729965, 642858091, 627401510, 612347805, 597685000, 583401543, 569486286, 555928471, 542717710, 529843973, 517297572, 505069147, 493149653, 481530348, 470202780, 459158776, 448390431, 437890097, 427650374, 417664099, 407924340, 398424383, 389157726, 380118071, 371299319, 362695555, 354301050, 346110249, 338117766, 330318378, 322707020, 315278776, 308028879, 300952702, 294045754, 287303674, 280722231, 274297314, 268024930, 261901203, 255922365, 250084756, 244384819, 238819098, 233384230, 228076950, 222894081, 217832533, 212889304, 208061469]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 915).prefactor = (1186332618341279/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 915).cutoff/(generalMeanRows 915).c)).2 =
    (341816277840951/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 915).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 915).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 915).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 915

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 915).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 915).criticalRate j.val*(generalMeanRows 915).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 915).c*(generalMeanRows 915).criticalPoint j.val)).2-
      (generalMeanRows 915).J/2-(generalMeanRows 915).error (generalMeanGrid j.val)+
      (generalMeanRows 915).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 915).c)).2-
      (generalMeanRows 915).J/2-(generalMeanRows 915).error 4 := by
  have he : (generalMeanRows 915).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 915) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 915)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0915

/-! Kernel-checked entropy margins for general spectral rectangle 916. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0916
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4914066341, 4741429283, 4576421119, 4418616383, 4267619307, 4123061230, 3984598287, 3851909341, 3724694130, 3602671601, 3485578402, 3373167524, 3265207068, 3161479123, 3061778752, 2965913057, 2873700333, 2784969292, 2699558344, 2617314953, 2538095025, 2461762361, 2388188140, 2317250452, 2248833858, 2182828988, 2119132163, 2057645053, 1998274347, 1940931460, 1885532247, 1831996747, 1780248941, 1730216522, 1681830685, 1635025930, 1589739880, 1545913100, 1503488943, 1462413396, 1422634934, 1384104393, 1346774836, 1310601444, 1275541399, 1241553783, 1208599479, 1176641077, 1145642791, 1115570373, 1086391039, 1058073394, 1030587363, 1003904128, 977996068, 952836694, 928400604, 904663424, 881601762, 859193161, 837416057, 816249732, 795674284, 775670579, 756220226, 737305534, 718909488, 701015715, 683608455, 666672536, 650193347, 634156813, 618549374, 603357960, 588569972, 574173260, 560156108, 546507210, 533215659, 520270925, 507662843, 495381598, 483417707, 471762013, 460405663, 449340102, 438557060, 428048539, 417806805, 407824374, 398094009, 388608701, 379361669, 370346347, 361556377, 352985601, 344628054, 336477955, 328529704, 320777871, 313217195, 305842571, 298649053, 291631839, 284786275, 278107843, 271592159, 265234969, 259032144, 252979673, 247073664, 241310336, 235686017, 230197140, 224840241, 219611951, 214508998, 209528203, 204666474, 199920804, 195288273]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 916).prefactor = (1203297573365443/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 916).cutoff/(generalMeanRows 916).c)).2 =
    (167541122829803/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 916).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 916).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 916).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 916

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 916).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 916).criticalRate j.val*(generalMeanRows 916).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 916).c*(generalMeanRows 916).criticalPoint j.val)).2-
      (generalMeanRows 916).J/2-(generalMeanRows 916).error (generalMeanGrid j.val)+
      (generalMeanRows 916).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 916).c)).2-
      (generalMeanRows 916).J/2-(generalMeanRows 916).error 4 := by
  have he : (generalMeanRows 916).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 916) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 916)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0916

/-! Kernel-checked entropy margins for general spectral rectangle 917. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0917
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5155134266, 4985837574, 4823850851, 4668765681, 4520202321, 4377807194, 4241250652, 4110224976, 3984442581, 3863634403, 3747548439, 3635948437, 3528612696, 3425332988, 3325913568, 3230170278, 3137929725, 3049028527, 2963312626, 2880636656, 2800863359, 2723863051, 2649513127, 2577697605, 2508306705, 2441236459, 2376388346, 2313668963, 2252989707, 2194266487, 2137419459, 2082372770, 2029054326, 1977395575, 1927331302, 1878799438, 1831740887, 1786099354, 1741821191, 1698855254, 1657152762, 1616667174, 1577354061, 1539171001, 1502077470, 1466034739, 1431005784, 1396955197, 1363849103, 1331655080, 1300342086, 1269880393, 1240241514, 1211398149, 1183324121, 1155994326, 1129384674, 1103472047, 1078234249, 1053649960, 1029698699, 1006360782, 983617286, 961450011, 939841450, 918774756, 898233711, 878202699, 858666680, 839611159, 821022170, 802886247, 785190403, 767922110, 751069281, 734620248, 718563745, 702888893, 687585183, 672642458, 658050903, 643801027, 629883652, 616289900, 603011180, 590039180, 577365850, 564983396, 552884271, 541061162, 529506983, 518214865, 507178150, 496390382, 485845299, 475536825, 465459066, 455606301, 445972976, 436553700, 427343235, 418336497, 409528542, 400914571, 392489917, 384250043, 376190541, 368307120, 360595612, 353051958, 345672212, 338452533, 331389184, 324478525, 317717016, 311101206, 304627739, 298293343, 292094832, 286029101, 280093128]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 917).prefactor = (934155443665469/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 917).cutoff/(generalMeanRows 917).c)).2 =
    (92904719277899/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 917).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 917).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 917).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 917

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 917).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 917).criticalRate j.val*(generalMeanRows 917).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 917).c*(generalMeanRows 917).criticalPoint j.val)).2-
      (generalMeanRows 917).J/2-(generalMeanRows 917).error (generalMeanGrid j.val)+
      (generalMeanRows 917).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 917).c)).2-
      (generalMeanRows 917).J/2-(generalMeanRows 917).error 4 := by
  have he : (generalMeanRows 917).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 917) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 917)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0917

/-! Kernel-checked entropy margins for general spectral rectangle 918. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0918
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5146643896, 4975378210, 4811537323, 4654706659, 4504500713, 4360560516, 4222551366, 4090160798, 3963096768, 3841086014, 3723872584, 3611216496, 3502892534, 3398689147, 3298407451, 3201860313, 3108871527, 3019275043, 2932914274, 2849641453, 2769317043, 2691809194, 2616993242, 2544751247, 2474971566, 2407548454, 2342381702, 2279376295, 2218442092, 2159493541, 2102449397, 2047232473, 1993769402, 1941990414, 1891829131, 1843222375, 1796109985, 1750434651, 1706141754, 1663179219, 1621497377, 1581048834, 1541788347, 1503672714, 1466660662, 1430712746, 1395791259, 1361860134, 1328884866, 1296832431, 1265671209, 1235370916, 1205902537, 1177238260, 1149351423, 1122216450, 1095808806, 1070104940, 1045082246, 1020719007, 996994364, 973888270, 951381452, 929455376, 908092217, 887274819, 866986670, 847211873, 827935116, 809141647, 790817252, 772948225, 755521353, 738523890, 721943540, 705768434, 689987117, 674588526, 659561976, 644897144, 630584053, 616613059, 602974840, 589660376, 576660943, 563968101, 551573679, 539469768, 527648708, 516103081, 504825701, 493809604, 483048041, 472534468, 462262541, 452226107, 442419197, 432836020, 423470955, 414318546, 405373499, 396630671, 388085066, 379731833, 371566259, 363583763, 355779892, 348150321, 340690841, 333397361, 326265902, 319292594, 312473671, 305805469, 299284424, 292907064, 286670011, 280569977, 274603759, 268768238, 263060377]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 918).prefactor = (4737185488318379/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 918).cutoff/(generalMeanRows 918).c)).2 =
    (72958582408239/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 918).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 918).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 918).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 918

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 918).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 918).criticalRate j.val*(generalMeanRows 918).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 918).c*(generalMeanRows 918).criticalPoint j.val)).2-
      (generalMeanRows 918).J/2-(generalMeanRows 918).error (generalMeanGrid j.val)+
      (generalMeanRows 918).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 918).c)).2-
      (generalMeanRows 918).J/2-(generalMeanRows 918).error 4 := by
  have he : (generalMeanRows 918).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 918) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 918)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0918

/-! Kernel-checked entropy margins for general spectral rectangle 919. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0919
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5083981515, 4916559774, 4756407217, 4603114581, 4456301484, 4315613904, 4180721918, 4051317694, 3927113671, 3807840938, 3693247758, 3583098245, 3477171156, 3375258796, 3277166024, 3182709346, 3091716082, 3004023608, 2919478663, 2837936705, 2759261328, 2683323716, 2610002149, 2539181542, 2470753016, 2404613507, 2340665401, 2278816195, 2218978184, 2161068169, 2105007182, 2050720241, 1998136108, 1947187074, 1897808749, 1849939878, 1803522158, 1758500069, 1714820724, 1672433718, 1631290992, 1591346705, 1552557112, 1514880456, 1478276853, 1442708202, 1408138083, 1374531676, 1341855671, 1310078196, 1279168741, 1249098087, 1219838245, 1191362389, 1163644805, 1136660830, 1110386802, 1084800014, 1059878663, 1035601813, 1011949347, 988901932, 966440981, 944548621, 923207653, 902401530, 882114318, 862330677, 843035827, 824215527, 805856049, 787944159, 770467090, 753412526, 736768580, 720523776, 704667034, 689187650, 674075282, 659319936, 644911947, 630841971, 617100970, 603680199, 590571193, 577765760, 565255966, 553034127, 541092800, 529424770, 518023047, 506880853, 495991614, 485348957, 474946697, 464778832, 454839538, 445123162, 435624212, 426337358, 417257421, 408379369, 399698312, 391209499, 382908311, 374790255, 366850965, 359086193, 351491805, 344063783, 336798212, 329691286, 322739298, 315938640, 309285797, 302777349, 296409963, 290180393, 284085475, 278122128, 272287348]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 919).prefactor = (2345978972253181/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 919).cutoff/(generalMeanRows 919).c)).2 =
    (95509878691323/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 919).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 919).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 919).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 919

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 919).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 919).criticalRate j.val*(generalMeanRows 919).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 919).c*(generalMeanRows 919).criticalPoint j.val)).2-
      (generalMeanRows 919).J/2-(generalMeanRows 919).error (generalMeanGrid j.val)+
      (generalMeanRows 919).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 919).c)).2-
      (generalMeanRows 919).J/2-(generalMeanRows 919).error 4 := by
  have he : (generalMeanRows 919).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 919) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 919)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0919

/-! Kernel-checked entropy margins for general spectral rectangle 920. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0920
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5223558146, 5051539975, 4886990559, 4729489396, 4578645664, 4434095619, 4295500282, 4162543369, 4034929424, 3912382154, 3794642910, 3681469331, 3572634099, 3467923816, 3367137987, 3270088076, 3176596665, 3086496665, 2999630606, 2915849979, 2835014632, 2756992214, 2681657663, 2608892733, 2538585556, 2470630240, 2404926490, 2341379264, 2279898449, 2220398560, 2162798464, 2107021119, 2052993331, 2000645532, 1949911565, 1900728493, 1853036411, 1806778277, 1761899751, 1718349043, 1676076776, 1635035851, 1595181321, 1556470282, 1518861757, 1482316597, 1446797384, 1412268340, 1378695241, 1346045342, 1314287292, 1283391072, 1253327924, 1224070287, 1195591739, 1167866940, 1140871580, 1114582327, 1088976781, 1064033429, 1039731604, 1016051440, 992973843, 970480445, 948553578, 927176239, 906332059, 886005273, 866180698, 846843702, 827980180, 809576534, 791619646, 774096862, 756995969, 740305178, 724013101, 708108744, 692581478, 677421035, 662617486, 648161231, 634042982, 620253754, 606784851, 593627855, 580774615, 568217235, 555948068, 543959702, 532244954, 520796859, 509608666, 498673823, 487985977, 477538961, 467326792, 457343661, 447583925, 438042108, 428712888, 419591096, 410671708, 401949842, 393420751, 385079821, 376922564, 368944616, 361141731, 353509778, 346044737, 338742696, 331599846, 324612481, 317776991, 311089859, 304547661, 298147062, 291884813, 285757747, 279762779]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 920).prefactor = (192830875321403/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 920).cutoff/(generalMeanRows 920).c)).2 =
    (95509878691323/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 920).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 920).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 920).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 920

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 920).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 920).criticalRate j.val*(generalMeanRows 920).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 920).c*(generalMeanRows 920).criticalPoint j.val)).2-
      (generalMeanRows 920).J/2-(generalMeanRows 920).error (generalMeanGrid j.val)+
      (generalMeanRows 920).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 920).c)).2-
      (generalMeanRows 920).J/2-(generalMeanRows 920).error 4 := by
  have he : (generalMeanRows 920).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 920) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 920)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0920

/-! Kernel-checked entropy margins for general spectral rectangle 921. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0921
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5282873992, 5106592063, 4937995473, 4776651791, 4622159070, 4474143185, 4332255452, 4196170500, 4065584363, 3940212759, 3819789542, 3704065297, 3592806074, 3485792228, 3382817369, 3283687409, 3188219681, 3096242139, 3007592627, 2922118200, 2839674506, 2760125216, 2683341499, 2609201529, 2537590046, 2468397933, 2401521833, 2336863792, 2274330930, 2213835129, 2155292749, 2098624361, 2043754499, 1990611426, 1939126922, 1889236078, 1840877112, 1793991188, 1748522252, 1704416883, 1661624139, 1620095428, 1579784380, 1540646726, 1502640183, 1465724357, 1429860636, 1395012098, 1361143428, 1328220832, 1296211958, 1265085826, 1234812757, 1205364309, 1176713216, 1148833327, 1121699556, 1095287826, 1069575023, 1044538950, 1020158281, 996412522, 973281972, 950747685, 928791435, 907395683, 886543548, 866218773, 846405700, 827089245, 808254865, 789888544, 771976763, 754506481, 737465113, 720840515, 704620957, 688795115, 673352046, 658281179, 643572292, 629215507, 615201267, 601520328, 588163749, 575122871, 562389316, 549954970, 537811973, 525952712, 514369809, 503056115, 492004697, 481208834, 470662007, 460357892, 450290353, 440453435, 430841359, 421448512, 412269445, 403298866, 394531633, 385962752, 377587367, 369400760, 361398346, 353575665, 345928380, 338452273, 331143242, 323997296, 317010549, 310179223, 303499638, 296968212, 290581459, 284335983, 278228477, 272255720, 266414576]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 921).prefactor = (619140288103823/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 921).cutoff/(generalMeanRows 921).c)).2 =
    (46916010022163/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 921).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 921).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 921).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 921

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 921).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 921).criticalRate j.val*(generalMeanRows 921).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 921).c*(generalMeanRows 921).criticalPoint j.val)).2-
      (generalMeanRows 921).J/2-(generalMeanRows 921).error (generalMeanGrid j.val)+
      (generalMeanRows 921).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 921).c)).2-
      (generalMeanRows 921).J/2-(generalMeanRows 921).error 4 := by
  have he : (generalMeanRows 921).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 921) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 921)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0921

/-! Kernel-checked entropy margins for general spectral rectangle 922. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0922
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7532045844, 7310243302, 7097005940, 6891895570, 6694504025, 6504450438, 6321378828, 6144955959, 5974869432, 5810825981, 5652549944, 5499781892, 5352277387, 5209805871, 5072149643, 4939102951, 4810471147, 4686069929, 4565724642, 4449269643, 4336547711, 4227409516, 4121713122, 4019323527, 3920112249, 3823956934, 3730740993, 3640353274, 3552687744, 3467643208, 3385123037, 3305034917, 3227290616, 3151805770, 3078499672, 3007295087, 2938118072, 2870897806, 2805566435, 2742058923, 2680312914, 2620268599, 2561868597, 2505057835, 2449783439, 2395994633, 2343642639, 2292680586, 2243063423, 2194747833, 2147692162, 2101856337, 2057201802, 2013691447, 1971289548, 1929961706, 1889674788, 1850396877, 1812097216, 1774746164, 1738315143, 1702776600, 1668103962, 1634271596, 1601254769, 1569029614, 1537573095, 1506862971, 1476877767, 1447596744, 1418999868, 1391067782, 1363781783, 1337123792, 1311076335, 1285622515, 1260745995, 1236430970, 1212662154, 1189424757, 1166704465, 1144487426, 1122760230, 1101509893, 1080723844, 1060389907, 1040496287, 1021031556, 1001984644, 983344820, 965101682, 947245148, 929765443, 912653085, 895898879, 879493908, 863429516, 847697309, 832289136, 817197090, 802413491, 787930886, 773742036, 759839910, 746217679, 732868710, 719786556, 706964955, 694397819, 682079230, 670003436, 658164843, 646558013, 635177655, 624018624, 613075914, 602344656, 591820108, 581497659, 571372818, 561441216]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 922).prefactor = (253312009309309/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 922).cutoff/(generalMeanRows 922).c)).2 =
    (847897450111/3125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 922).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 922).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 922).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 922

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 922).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 922).criticalRate j.val*(generalMeanRows 922).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 922).c*(generalMeanRows 922).criticalPoint j.val)).2-
      (generalMeanRows 922).J/2-(generalMeanRows 922).error (generalMeanGrid j.val)+
      (generalMeanRows 922).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 922).c)).2-
      (generalMeanRows 922).J/2-(generalMeanRows 922).error 4 := by
  have he : (generalMeanRows 922).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 922) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 922)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0922

/-! Kernel-checked entropy margins for general spectral rectangle 923. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0923
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7284066517, 7071116248, 6866468700, 6669694947, 6480395449, 6298197409, 6122752423, 5953734399, 5790837688, 5633775430, 5482278056, 5336091946, 5194978219, 5058711639, 4927079620, 4799881325, 4676926847, 4558036459, 4443039926, 4331775885, 4224091262, 4119840747, 4018886306, 3921096733, 3826347232, 3734519037, 3645499052, 3559179526, 3475457742, 3394235735, 3315420027, 3238921378, 3164654555, 3092538118, 3022494219, 2954448410, 2888329470, 2824069235, 2761602448, 2700866606, 2641801829, 2584350726, 2528458275, 2474071708, 2421140404, 2369615785, 2319451219, 2270601931, 2223024917, 2176678860, 2131524055, 2087522334, 2044637001, 2002832760, 1962075657, 1922333021, 1883573407, 1845766542, 1808883274, 1772895528, 1737776254, 1703499388, 1670039810, 1637373303, 1605476514, 1574326925, 1543902810, 1514183208, 1485147892, 1456777336, 1429052690, 1401955751, 1375468939, 1349575270, 1324258335, 1299502276, 1275291765, 1251611983, 1228448602, 1205787763, 1183616062, 1161920528, 1140688613, 1119908169, 1099567438, 1079655036, 1060159938, 1041071467, 1022379280, 1004073354, 986143978, 968581738, 951377509, 934522444, 918007964, 901825746, 885967719, 870426049, 855193138, 840261608, 825624299, 811274259, 797204736, 783409174, 769881206, 756614642, 743603472, 730841852, 718324104, 706044706, 693998290, 682179637, 670583668, 659205446, 648040165, 637083149, 626329849, 615775835, 605416796, 595248534, 585266960]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 923).prefactor = (4956911083580547/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 923).cutoff/(generalMeanRows 923).c)).2 =
    (147599810121/500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 923).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 923).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 923).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 923

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 923).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 923).criticalRate j.val*(generalMeanRows 923).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 923).c*(generalMeanRows 923).criticalPoint j.val)).2-
      (generalMeanRows 923).J/2-(generalMeanRows 923).error (generalMeanGrid j.val)+
      (generalMeanRows 923).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 923).c)).2-
      (generalMeanRows 923).J/2-(generalMeanRows 923).error 4 := by
  have he : (generalMeanRows 923).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 923) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 923)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0923

/-! Kernel-checked entropy margins for general spectral rectangle 924. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0924
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7095204000, 6891642976, 6696084835, 6508111121, 6327332106, 6153384211, 5985927732, 5824644806, 5669237602, 5519426697, 5374949621, 5235559546, 5101024100, 4971124299, 4845653571, 4724416878, 4607229906, 4493918335, 4384317162, 4278270087, 4175628948, 4076253200, 3980009436, 3886770942, 3796417294, 3708833975, 3623912026, 3541547721, 3461642265, 3384101513, 3308835708, 3235759238, 3164790405, 3095851218, 3028867189, 2963767149, 2900483072, 2838949914, 2779105456, 2720890164, 2664247048, 2609121541, 2555461372, 2503216459, 2452338796, 2402782359, 2354503007, 2307458392, 2261607877, 2216912454, 2173334669, 2130838546, 2089389528, 2048954403, 2009501250, 1970999377, 1933419266, 1896732525, 1860911834, 1825930899, 1791764410, 1758387993, 1725778176, 1693912347, 1662768716, 1632326284, 1602564806, 1573464763, 1545007328, 1517174341, 1489948280, 1463312233, 1437249876, 1411745449, 1386783730, 1362350017, 1338430108, 1315010275, 1292077252, 1269618215, 1247620761, 1226072897, 1204963022, 1184279909, 1164012694, 1144150864, 1124684237, 1105602957, 1086897475, 1068558543, 1050577200, 1032944761, 1015652809, 998693182, 982057968, 965739490, 949730304, 934023186, 918611126, 903487319, 888645160, 874078235, 859780315, 845745349, 831967459, 818440933, 805160218, 792119919, 779314787, 766739722, 754389760, 742260073, 730345966, 718642866, 707146326, 695852014, 684755714, 673853319, 663140831, 652614353, 642270090]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 924).prefactor = (966833045611653/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 924).cutoff/(generalMeanRows 924).c)).2 =
    (20327060927601/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 924).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 924).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 924).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 924

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 924).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 924).criticalRate j.val*(generalMeanRows 924).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 924).c*(generalMeanRows 924).criticalPoint j.val)).2-
      (generalMeanRows 924).J/2-(generalMeanRows 924).error (generalMeanGrid j.val)+
      (generalMeanRows 924).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 924).c)).2-
      (generalMeanRows 924).J/2-(generalMeanRows 924).error 4 := by
  have he : (generalMeanRows 924).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 924) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 924)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0924

/-! Kernel-checked entropy margins for general spectral rectangle 925. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0925
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6590417592, 6388639075, 6194940028, 6008897726, 5830118378, 5658234551, 5492902873, 5333802003, 5180630803, 5033106714, 4890964283, 4753953855, 4621840369, 4494402289, 4371430619, 4252728014, 4138107971, 4027394084, 3920419370, 3817025641, 3717062940, 3620389012, 3526868819, 3436374096, 3348782936, 3263979410, 3181853209, 3102299320, 3025217718, 2950513081, 2878094529, 2807875373, 2739772886, 2673708091, 2609605555, 2547393205, 2487002146, 2428366503, 2371423257, 2316112107, 2262375327, 2210157642, 2159406100, 2110069965, 2062100603, 2015451383, 1970077581, 1925936290, 1882986330, 1841188174, 1800503863, 1760896941, 1722332382, 1684776526, 1648197016, 1612562742, 1577843784, 1544011357, 1511037766, 1478896355, 1447561462, 1417008376, 1387213297, 1358153297, 1329806284, 1302150963, 1275166806, 1248834021, 1223133516, 1198046877, 1173556335, 1149644741, 1126295544, 1103492761, 1081220961, 1059465235, 1038211184, 1017444891, 997152909, 977322236, 957940302, 938994952, 920474429, 902367357, 884662730, 867349897, 850418545, 833858693, 817660674, 801815123, 786312972, 771145433, 756303988, 741780385, 727566621, 713654937, 700037809, 686707939, 673658246, 660881862, 648372120, 636122548, 624126865, 612378971, 600872944, 589603029, 578563638, 567749341, 557154861, 546775070, 536604982, 526639749, 516874660, 507305130, 497926700, 488735034, 479725911, 470895224, 462238976, 453753276, 445434336]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 925).prefactor = (304595204299501/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 925).cutoff/(generalMeanRows 925).c)).2 =
    (149309663161763/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 925).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 925).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 925).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 925

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 925).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 925).criticalRate j.val*(generalMeanRows 925).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 925).c*(generalMeanRows 925).criticalPoint j.val)).2-
      (generalMeanRows 925).J/2-(generalMeanRows 925).error (generalMeanGrid j.val)+
      (generalMeanRows 925).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 925).c)).2-
      (generalMeanRows 925).J/2-(generalMeanRows 925).error 4 := by
  have he : (generalMeanRows 925).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 925) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 925)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0925

/-! Kernel-checked entropy margins for general spectral rectangle 926. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0926
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6454992444, 6263266869, 6079257073, 5902553545, 5732774940, 5569565582, 5412593242, 5261547162, 5116136286, 4976087676, 4841145083, 4711067668, 4585628836, 4464615185, 4347825550, 4235070134, 4126169715, 4020954919, 3919265559, 3820950025, 3725864725, 3633873570, 3544847498, 3458664039, 3375206909, 3294365633, 3216035200, 3140115740, 3066512224, 2995134182, 2925895451, 2858713924, 2793511330, 2730213021, 2668747773, 2609047605, 2551047602, 2494685755, 2439902808, 2386642114, 2334849504, 2284473157, 2235463483, 2187773010, 2141356282, 2096169752, 2052171698, 2009322127, 1967582694, 1926916623, 1887288634, 1848664868, 1811012826, 1774301300, 1738500317, 1703581081, 1669515920, 1636278232, 1603842440, 1572183945, 1541279083, 1511105080, 1481640020, 1452862798, 1424753093, 1397291330, 1370458648, 1344236869, 1318608473, 1293556564, 1269064847, 1245117605, 1221699670, 1198796403, 1176393674, 1154477836, 1133035710, 1112054565, 1091522099, 1071426420, 1051756035, 1032499828, 1013647050, 995187303, 977110522, 959406971, 942067222, 925082148, 908442908, 892140940, 876167947, 860515890, 845176974, 830143644, 815408575, 800964658, 786805001, 772922914, 759311904, 745965670, 732878092, 720043229, 707455310, 695108725, 682998029, 671117924, 659463264, 648029044, 636810398, 625802593, 615001022, 604401207, 593998787, 583789517, 573769268, 563934014, 554279840, 544802929, 535499563, 526366121, 517399072]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 926).prefactor = (4724840282387099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 926).cutoff/(generalMeanRows 926).c)).2 =
    (336207643969377/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 926).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 926).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 926).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 926

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 926).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 926).criticalRate j.val*(generalMeanRows 926).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 926).c*(generalMeanRows 926).criticalPoint j.val)).2-
      (generalMeanRows 926).J/2-(generalMeanRows 926).error (generalMeanGrid j.val)+
      (generalMeanRows 926).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 926).c)).2-
      (generalMeanRows 926).J/2-(generalMeanRows 926).error 4 := by
  have he : (generalMeanRows 926).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 926) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 926)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0926

/-! Kernel-checked entropy margins for general spectral rectangle 927. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0927
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6117250695, 5928148846, 5746766929, 5572693790, 5405546538, 5244968045, 5090624733, 4942204583, 4799415372, 4661983080, 4529650461, 4402175757, 4279331528, 4160903599, 4046690097, 3936500581, 3830155241, 3727484172, 3628326705, 3532530798, 3439952467, 3350455274, 3263909847, 3180193441, 3099189526, 3020787414, 2944881908, 2871372976, 2800165449, 2731168745, 2664296598, 2599466824, 2536601089, 2475624693, 2416466380, 2359058142, 2303335052, 2249235099, 2196699031, 2145670217, 2096094507, 2047920108, 2001097462, 1955579135, 1911319712, 1868275692, 1826405402, 1785668899, 1746027894, 1707445666, 1669886993, 1633318074, 1597706471, 1563021036, 1529231858, 1496310202, 1464228459, 1432960088, 1402479576, 1372762385, 1343784912, 1315524446, 1287959129, 1261067919, 1234830554, 1209227517, 1184240008, 1159849906, 1136039747, 1112792693, 1090092506, 1067923523, 1046270631, 1025119246, 1004455290, 984265170, 964535759, 945254379, 926408777, 907987114, 889977946, 872370209, 855153201, 838316574, 821850313, 805744729, 789990444, 774578377, 759499736, 744746007, 730308941, 716180545, 702353072, 688819016, 675571096, 662602254, 649905643, 637474621, 625302743, 613383755, 601711586, 590280342, 579084299, 568117899, 557375741, 546852579, 536543316, 526442994, 516546798, 506850044, 497348177, 488036767, 478911505, 469968198, 461202766, 452611238, 444189748, 435934532, 427841926, 419908361, 412130359]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 927).prefactor = (4737518948743339/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 927).cutoff/(generalMeanRows 927).c)).2 =
    (1015789323099/3125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 927).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 927).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 927).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 927

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 927).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 927).criticalRate j.val*(generalMeanRows 927).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 927).c*(generalMeanRows 927).criticalPoint j.val)).2-
      (generalMeanRows 927).J/2-(generalMeanRows 927).error (generalMeanGrid j.val)+
      (generalMeanRows 927).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 927).c)).2-
      (generalMeanRows 927).J/2-(generalMeanRows 927).error 4 := by
  have he : (generalMeanRows 927).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 927) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 927)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0927

/-! Kernel-checked entropy margins for general spectral rectangle 928. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0928
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5747212036, 5561629980, 5383755228, 5213175555, 5049507056, 4892391650, 4741494861, 4596503842, 4457125596, 4323085394, 4194125339, 4070003076, 3950490625, 3835373322, 3724448854, 3617526388, 3514425765, 3414976771, 3319018470, 3226398583, 3136972930, 3050604904, 2967164992, 2886530337, 2808584322, 2733216194, 2660320710, 2589797814, 2521552332, 2455493686, 2391535638, 2329596039, 2269596602, 2211462691, 2155123116, 2100509949, 2047558350, 1996206401, 1946394951, 1898067474, 1851169930, 1805650642, 1761460170, 1718551203, 1676878449, 1636398537, 1597069921, 1558852791, 1521708988, 1485601925, 1450496515, 1416359092, 1383157350, 1350860280, 1319438105, 1288862225, 1259105165, 1230140521, 1201942911, 1174487932, 1147752114, 1121712878, 1096348498, 1071638063, 1047561440, 1024099243, 1001232798, 978944114, 957215854, 936031304, 915374352, 895229460, 875581638, 856416425, 837719864, 819478486, 801679284, 784309697, 767357594, 750811254, 734659350, 718890936, 703495428, 688462592, 673782531, 659445669, 645442744, 631764790, 618403128, 605349357, 592595341, 580133200, 567955301, 556054247, 544422872, 533054226, 521941576, 511078390, 500458334, 490075264, 479923219, 469996415, 460289239, 450796241, 441512132, 432431773, 423550176, 414862494, 406364020, 398050177, 389916522, 381958731, 374172604, 366554056, 359099115, 351803917, 344664706, 337677824, 330839715, 324146916, 317596059]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 928).prefactor = (118503049689231/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 928).cutoff/(generalMeanRows 928).c)).2 =
    (311971131728987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 928).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 928).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 928).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 928

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 928).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 928).criticalRate j.val*(generalMeanRows 928).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 928).c*(generalMeanRows 928).criticalPoint j.val)).2-
      (generalMeanRows 928).J/2-(generalMeanRows 928).error (generalMeanGrid j.val)+
      (generalMeanRows 928).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 928).c)).2-
      (generalMeanRows 928).J/2-(generalMeanRows 928).error 4 := by
  have he : (generalMeanRows 928).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 928) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 928)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0928

/-! Kernel-checked entropy margins for general spectral rectangle 929. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0929
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5760121959, 5584680732, 5416499015, 5255181518, 5100360395, 4951692832, 4808858898, 4671559629, 4539515310, 4412463929, 4290159795, 4172372273, 4058884656, 3949493132, 3844005846, 3742242046, 3644031304, 3549212805, 3457634689, 3369153455, 3283633409, 3200946152, 3120970120, 3043590144, 2968697053, 2896187305, 2825962641, 2757929769, 2692000068, 2628089310, 2566117407, 2506008171, 2447689091, 2391091124, 2336148502, 2282798552, 2230981522, 2180640423, 2131720883, 2084171000, 2037941217, 1992984197, 1949254704, 1906709496, 1865307224, 1825008330, 1785774963, 1747570887, 1710361404, 1674113275, 1638794650, 1604375000, 1570825049, 1538116719, 1506223069, 1475118241, 1444777408, 1415176729, 1386293298, 1358105104, 1330590988, 1303730603, 1277504380, 1251893490, 1226879811, 1202445897, 1178574948, 1155250780, 1132457800, 1110180977, 1088405822, 1067118359, 1046305109, 1025953063, 1006049668, 986582801, 967540757, 948912227, 930686287, 912852374, 895400280, 878320133, 861602381, 845237786, 829217405, 813532583, 798174936, 783136349, 768408955, 753985136, 739857504, 726018899, 712462377, 699181204, 686168844, 673418958, 660925391, 648682168, 636683487, 624923712, 613397369, 602099139, 591023851, 580166478, 569522135, 559086068, 548853655, 538820397, 528981919, 519333960, 509872373, 500593121, 491492273, 482565998, 473810565, 465222338, 456797776, 448533425, 440425918, 432471974, 424668390]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 929).prefactor = (4564032513349231/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 929).cutoff/(generalMeanRows 929).c)).2 =
    (182818931753379/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 929).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 929).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 929).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 929

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 929).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 929).criticalRate j.val*(generalMeanRows 929).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 929).c*(generalMeanRows 929).criticalPoint j.val)).2-
      (generalMeanRows 929).J/2-(generalMeanRows 929).error (generalMeanGrid j.val)+
      (generalMeanRows 929).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 929).c)).2-
      (generalMeanRows 929).J/2-(generalMeanRows 929).error 4 := by
  have he : (generalMeanRows 929).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 929) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 929)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0929

/-! Kernel-checked entropy margins for general spectral rectangle 930. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0930
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5530091439, 5358114573, 5193327403, 5035336108, 4883774277, 4738300499, 4598596229, 4464363865, 4335325042, 4211219082, 4091801615, 3976843315, 3866128773, 3759455458, 3656632786, 3557481262, 3461831700, 3369524511, 3280409045, 3194342995, 3111191841, 3030828343, 2953132074, 2877988982, 2805290995, 2734935646, 2666825733, 2600868996, 2536977825, 2475068982, 2415063345, 2356885669, 2300464364, 2245731285, 2192621540, 2141073306, 2091027663, 2042428430, 1995222017, 1949357288, 1904785426, 1861459813, 1819335913, 1778371161, 1738524865, 1699758104, 1662033644, 1625315847, 1589570594, 1554765206, 1520868376, 1487850098, 1455681604, 1424335306, 1393784737, 1364004497, 1334970203, 1306658438, 1279046712, 1252113409, 1225837758, 1200199782, 1175180270, 1150760739, 1126923402, 1103651133, 1080927443, 1058736449, 1037062845, 1015891880, 995209333, 975001488, 955255116, 935957451, 917096170, 898659376, 880635581, 863013685, 845782965, 828933055, 812453933, 796335909, 780569607, 765145959, 750056184, 735291786, 720844535, 706706463, 692869846, 679327205, 666071285, 653095057, 640391703, 627954609, 615777360, 603853728, 592177672, 580743324, 569544986, 558577126, 547834368, 537311489, 527003412, 516905202, 507012062, 497319326, 487822455, 478517035, 469398769, 460463477, 451707089, 443125643, 434715281, 426472245, 418392875, 410473606, 402710963, 395101559, 387642094, 380329351, 373160192]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 930).prefactor = (568485038376999/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 930).cutoff/(generalMeanRows 930).c)).2 =
    (36629554192573/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 930).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 930).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 930).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 930

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 930).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 930).criticalRate j.val*(generalMeanRows 930).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 930).c*(generalMeanRows 930).criticalPoint j.val)).2-
      (generalMeanRows 930).J/2-(generalMeanRows 930).error (generalMeanGrid j.val)+
      (generalMeanRows 930).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 930).c)).2-
      (generalMeanRows 930).J/2-(generalMeanRows 930).error 4 := by
  have he : (generalMeanRows 930).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 930) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 930)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0930

/-! Kernel-checked entropy margins for general spectral rectangle 931. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0931
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5265009582, 5096994700, 4936088970, 4781900636, 4634065274, 4492243399, 4356118327, 4225394273, 4099794635, 3979060461, 3862949065, 3751232770, 3643697774, 3540143127, 3440379788, 3344229771, 3251525370, 3162108441, 3075829749, 2992548371, 2912131138, 2834452131, 2759392211, 2686838585, 2616684407, 2548828406, 2483174547, 2419631704, 2358113372, 2298537388, 2240825676, 2184904006, 2130701776, 2078151799, 2027190114, 1977755802, 1929790817, 1883239827, 1838050067, 1794171196, 1751555171, 1710156120, 1669930231, 1630835639, 1592832329, 1555882035, 1519948157, 1484995669, 1450991041, 1417902168, 1385698294, 1354349946, 1323828872, 1294107981, 1265161285, 1236963848, 1209491734, 1182721959, 1156632447, 1131201989, 1106410198, 1082237473, 1058664966, 1035674542, 1013248750, 991370792, 970024492, 949194269, 928865111, 909022550, 889652639, 870741925, 852277435, 834246649, 816637483, 799438272, 782637749, 766225031, 750189605, 734521306, 719210310, 704247116, 689622534, 675327672, 661353925, 647692965, 634336725, 621277396, 608507410, 596019436, 583806368, 571861318, 560177607, 548748757, 537568483, 526630689, 515929456, 505459042, 495213868, 485188519, 475377735, 465776404, 456379559, 447182376, 438180161, 429368353, 420742515, 412298334, 404031610, 395938262, 388014314, 380255898, 372659248, 365220699, 357936680, 350803713, 343818411, 336977476, 330277690, 323715921, 317289114]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 931).prefactor = (452430138540919/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 931).cutoff/(generalMeanRows 931).c)).2 =
    (72958582408239/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 931).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 931).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 931).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 931

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 931).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 931).criticalRate j.val*(generalMeanRows 931).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 931).c*(generalMeanRows 931).criticalPoint j.val)).2-
      (generalMeanRows 931).J/2-(generalMeanRows 931).error (generalMeanGrid j.val)+
      (generalMeanRows 931).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 931).c)).2-
      (generalMeanRows 931).J/2-(generalMeanRows 931).error 4 := by
  have he : (generalMeanRows 931).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 931) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 931)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0931

/-! Kernel-checked entropy margins for general spectral rectangle 932. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0932
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5211791842, 5047129542, 4889451274, 4738368859, 4593521355, 4454572676, 4321209457, 4193139161, 4070088367, 3951801236, 3838038130, 3728574359, 3623199051, 3521714120, 3423933332, 3329681449, 3238793455, 3151113835, 3066495927, 2984801321, 2905899305, 2829666357, 2755985678, 2684746760, 2615844983, 2549181246, 2484661626, 2422197057, 2361703037, 2303099352, 2246309820, 2191262054, 2137887239, 2086119930, 2035897850, 1987161718, 1939855076, 1893924133, 1849317613, 1805986625, 1763884525, 1722966797, 1683190942, 1644516365, 1606904279, 1570317608, 1534720897, 1500080231, 1466363154, 1433538594, 1401576795, 1370449250, 1340128637, 1310588763, 1281804507, 1253751767, 1226407412, 1199749236, 1173755908, 1148406939, 1123682636, 1099564064, 1076033018, 1053071981, 1030664095, 1008793134, 987443472, 966600055, 946248381, 926374467, 906964835, 888006483, 869486868, 851393885, 833715848, 816441473, 799559859, 783060475, 766933141, 751168018, 735755588, 720686646, 705952286, 691543886, 677453102, 663671852, 650192308, 637006886, 624108237, 611489236, 599142976, 587062756, 575242079, 563674638, 552354315, 541275167, 530431427, 519817494, 509427924, 499257433, 489300880, 479553273, 470009756, 460665608, 451516238, 442557177, 433784081, 425192720, 416778977, 408538846, 400468424, 392563913, 384821610, 377237911, 369809304, 362532365, 355403758, 348420232, 341578617, 334875820, 328308828]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 932).prefactor = (898786176584061/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 932).cutoff/(generalMeanRows 932).c)).2 =
    (190914549596881/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 932).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 932).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 932).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 932

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 932).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 932).criticalRate j.val*(generalMeanRows 932).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 932).c*(generalMeanRows 932).criticalPoint j.val)).2-
      (generalMeanRows 932).J/2-(generalMeanRows 932).error (generalMeanGrid j.val)+
      (generalMeanRows 932).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 932).c)).2-
      (generalMeanRows 932).J/2-(generalMeanRows 932).error 4 := by
  have he : (generalMeanRows 932).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 932) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 932)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0932

/-! Kernel-checked entropy margins for general spectral rectangle 933. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0933
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5169785359, 5000156646, 4837806981, 4682332783, 4533358683, 4390535055, 4253535816, 4122056456, 3995812280, 3874536812, 3757980374, 3645908784, 3538102191, 3434354008, 3334469942, 3238267117, 3145573261, 3056225974, 2970072048, 2886966847, 2806773736, 2729363557, 2654614139, 2582409857, 2512641212, 2445204452, 2380001215, 2316938197, 2255926851, 2196883100, 2139727072, 2084382851, 2030778254, 1978844608, 1928516556, 1879731868, 1832431265, 1786558254, 1742058980, 1698882074, 1656978527, 1616301556, 1576806490, 1538450656, 1501193275, 1464995364, 1429819641, 1395630441, 1362393630, 1330076529, 1298647845, 1268077592, 1238337039, 1209398636, 1181235965, 1153823683, 1127137465, 1101153964, 1075850759, 1051206309, 1027199920, 1003811698, 981022514, 958813970, 937168366, 916068667, 895498471, 875441987, 855884001, 836809855, 818205419, 800057071, 782351675, 765076558, 748219491, 731768671, 715712703, 700040581, 684741674, 669805711, 655222762, 640983230, 627077833, 613497594, 600233826, 587278124, 574622353, 562258634, 550179338, 538377077, 526844689, 515575236, 504561993, 493798439, 483278249, 472995291, 462943614, 453117444, 443511175, 434119369, 424936742, 415958166, 407178656, 398593372, 390197611, 381986801, 373956499, 366102385, 358420257, 350906030, 343555732, 336365494, 329331557, 322450259, 315718037, 309131422, 302687038, 296381597, 290211895, 284174814, 278267314]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 933).prefactor = (926721556204839/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 933).cutoff/(generalMeanRows 933).c)).2 =
    (361256090076047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 933).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 933).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 933).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 933

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 933).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 933).criticalRate j.val*(generalMeanRows 933).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 933).c*(generalMeanRows 933).criticalPoint j.val)).2-
      (generalMeanRows 933).J/2-(generalMeanRows 933).error (generalMeanGrid j.val)+
      (generalMeanRows 933).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 933).c)).2-
      (generalMeanRows 933).J/2-(generalMeanRows 933).error 4 := by
  have he : (generalMeanRows 933).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 933) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 933)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0933

/-! Kernel-checked entropy margins for general spectral rectangle 934. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0934
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5084826162, 4913605628, 4749792537, 4592976612, 4442776191, 4298835734, 4160823587, 4028429988, 3901365282, 3779358309, 3662154956, 3549516843, 3441220140, 3337054482, 3236821993, 3140336390, 3047422162, 2957913826, 2871655239, 2788498971, 2708305720, 2630943787, 2556288576, 2484222145, 2414632787, 2347414634, 2282467306, 2219695571, 2159009034, 2100321851, 2043552460, 1988623330, 1935460726, 1883994495, 1834157858, 1785887225, 1739122012, 1693804480, 1649879575, 1607294783, 1565999993, 1525947371, 1487091233, 1449387940, 1412795785, 1377274893, 1342787131, 1309296015, 1276766629, 1245165542, 1214460740, 1184621549, 1155618575, 1127423636, 1100009706, 1073350860, 1047422219, 1022199902, 997660975, 973783412, 950546049, 927928546, 905911347, 884475644, 863603347, 843277046, 823479984, 804196027, 785409638, 767105847, 749270229, 731888881, 714948397, 698435848, 682338763, 666645105, 651343261, 636422015, 621870539, 607678371, 593835405, 580331875, 567158339, 554305669, 541765037, 529527903, 517586005, 505931346, 494556187, 483453032, 472614626, 462033937, 451704156, 441618683, 431771120, 422155268, 412765113, 403594824, 394638746, 385891389, 377347430, 369001700, 360849183, 352885007, 345104443, 337502896, 330075906, 322819135, 315728372, 308799521, 302028604, 295411751, 288945200, 282625293, 276448472, 270411275, 264510336, 258742377, 253104211, 247592734, 242204926]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 934).prefactor = (4701927814794019/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 934).cutoff/(generalMeanRows 934).c)).2 =
    (347650438020269/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 934).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 934).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 934).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 934

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 934).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 934).criticalRate j.val*(generalMeanRows 934).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 934).c*(generalMeanRows 934).criticalPoint j.val)).2-
      (generalMeanRows 934).J/2-(generalMeanRows 934).error (generalMeanGrid j.val)+
      (generalMeanRows 934).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 934).c)).2-
      (generalMeanRows 934).J/2-(generalMeanRows 934).error 4 := by
  have he : (generalMeanRows 934).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 934) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 934)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0934

/-! Kernel-checked entropy margins for general spectral rectangle 935. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0935
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5288153809, 5121078914, 4961090381, 4807794342, 4660824566, 4519840043, 4384522817, 4254576065, 4129722359, 4009702112, 3894272175, 3783204567, 3676285325, 3573313460, 3474100010, 3378467171, 3286247506, 3197283224, 3111425515, 3028533939, 2948475868, 2871125973, 2796365742, 2724083048, 2654171738, 2586531259, 2521066312, 2457686527, 2396306163, 2336843830, 2279222231, 2223367918, 2169211068, 2116685276, 2065727354, 2016277151, 1968277384, 1921673470, 1876413387, 1832447523, 1789728552, 1748211308, 1707852666, 1668611438, 1630448268, 1593325538, 1557207272, 1522059059, 1487847967, 1454542470, 1422112374, 1390528755, 1359763891, 1329791206, 1300585209, 1272121447, 1244376450, 1217327684, 1190953508, 1165233132, 1140146573, 1115674622, 1091798805, 1068501347, 1045765147, 1023573738, 1001911265, 980762456, 960112593, 939947491, 920253474, 901017348, 882226388, 863868311, 845931260, 828403784, 811274825, 794533696, 778170068, 762173958, 746535708, 731245980, 716295735, 701676227, 687378988, 673395818, 659718775, 646340163, 633252526, 620448635, 607921480, 595664264, 583670393, 571933469, 560447282, 549205805, 538203186, 527433739, 516891944, 506572437, 496470003, 486579577, 476896230, 467415174, 458131749, 449041422, 440139785, 431422545, 422885526, 414524662, 406335995, 398315668, 390459927, 382765114, 375227664, 367844105, 360611052, 353525205, 346583347, 339782343, 333119132]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 935).prefactor = (4559774917200131/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 935).cutoff/(generalMeanRows 935).c)).2 =
    (190914549596881/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 935).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 935).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 935).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 935

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 935).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 935).criticalRate j.val*(generalMeanRows 935).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 935).c*(generalMeanRows 935).criticalPoint j.val)).2-
      (generalMeanRows 935).J/2-(generalMeanRows 935).error (generalMeanGrid j.val)+
      (generalMeanRows 935).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 935).c)).2-
      (generalMeanRows 935).J/2-(generalMeanRows 935).error 4 := by
  have he : (generalMeanRows 935).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 935) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 935)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0935

/-! Kernel-checked entropy margins for general spectral rectangle 936. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0936
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5281813656, 5112643796, 4950676234, 4795511009, 4646776198, 4504125456, 4367235831, 4235805803, 4109553534, 3988215284, 3871543991, 3759307983, 3651289815, 3547285204, 3447102074, 3350559672, 3257487769, 3167725924, 3081122814, 2997535611, 2916829423, 2838876760, 2763557063, 2690756249, 2620366308, 2552284913, 2486415075, 2422664813, 2360946847, 2301178320, 2243280529, 2187178689, 2132801694, 2080081914, 2028954990, 1979359650, 1931237534, 1884533035, 1839193145, 1795167310, 1752407299, 1710867080, 1670502698, 1631272169, 1593135374, 1556053959, 1519991249, 1484912156, 1450783100, 1417571934, 1385247868, 1353781404, 1323144270, 1293309360, 1264250677, 1235943278, 1208363225, 1181487535, 1155294134, 1129761814, 1104870195, 1080599682, 1056931432, 1033847317, 1011329893, 989362366, 967928568, 947012921, 926600419, 906676596, 887227507, 868239702, 849700206, 831596498, 813916492, 796648518, 779781306, 763303967, 747205977, 731477165, 716107695, 701088054, 686409041, 672061750, 658037560, 644328126, 630925365, 617821449, 605008790, 592480038, 580228065, 568245961, 556527023, 545064750, 533852833, 522885150, 512155758, 501658886, 491388931, 481340449, 471508151, 461886900, 452471699, 443257695, 434240165, 425414518, 416776290, 408321136, 400044828, 391943253, 384012407, 376248392, 368647412, 361205771, 353919869, 346786199, 339801344, 332961976, 326264850, 319706802, 313284751]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 936).prefactor = (2313291841508743/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 936).cutoff/(generalMeanRows 936).c)).2 =
    (374979757348187/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 936).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 936).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 936).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 936

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 936).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 936).criticalRate j.val*(generalMeanRows 936).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 936).c*(generalMeanRows 936).criticalPoint j.val)).2-
      (generalMeanRows 936).J/2-(generalMeanRows 936).error (generalMeanGrid j.val)+
      (generalMeanRows 936).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 936).c)).2-
      (generalMeanRows 936).J/2-(generalMeanRows 936).error 4 := by
  have he : (generalMeanRows 936).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 936) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 936)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0936

/-! Kernel-checked entropy margins for general spectral rectangle 937. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0937
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5221244874, 5055925235, 4897655792, 4746041546, 4600715364, 4461335538, 4327583610, 4199162424, 4075794375, 3957219840, 3843195759, 3733494353, 3627901960, 3526217984, 3428253930, 3333832533, 3242786954, 3154960051, 3070203706, 2988378213, 2909351707, 2832999645, 2759204327, 2687854447, 2618844692, 2552075353, 2487451980, 2424885052, 2364289677, 2305585313, 2248695499, 2193547620, 2140072675, 2088205068, 2037882409, 1989045332, 1941637321, 1895604550, 1850895732, 1807461978, 1765256664, 1724235310, 1684355460, 1645576576, 1607859933, 1571168526, 1535466977, 1500721450, 1466899572, 1433970357, 1401904138, 1370672494, 1340248192, 1310605127, 1281718266, 1253563591, 1226118056, 1199359534, 1173266777, 1147819369, 1122997692, 1098782884, 1075156804, 1052102000, 1029601676, 1007639663, 986200389, 965268852, 944830594, 924871679, 905378667, 886338595, 867738953, 849567666, 831813076, 814463923, 797509328, 780938777, 764742107, 748909490, 733431420, 718298699, 703502425, 689033982, 674885023, 661047466, 647513480, 634275475, 621326094, 608658203, 596264884, 584139426, 572275314, 560666230, 549306035, 538188772, 527308653, 516660057, 506237521, 496035736, 486049540, 476273918, 466703989, 457335007, 448162354, 439181539, 430388188, 421778045, 413346967, 405090919, 397005971, 389088296, 381334165, 373739944, 366302092, 359017158, 351881777, 344892668, 338046635, 331340555, 324771388]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 937).prefactor = (458327831372957/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 937).cutoff/(generalMeanRows 937).c)).2 =
    (392963789007893/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 937).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 937).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 937).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 937

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 937).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 937).criticalRate j.val*(generalMeanRows 937).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 937).c*(generalMeanRows 937).criticalPoint j.val)).2-
      (generalMeanRows 937).J/2-(generalMeanRows 937).error (generalMeanGrid j.val)+
      (generalMeanRows 937).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 937).c)).2-
      (generalMeanRows 937).J/2-(generalMeanRows 937).error 4 := by
  have he : (generalMeanRows 937).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 937) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 937)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0937

/-! Kernel-checked entropy margins for general spectral rectangle 938. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0938
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5202348180, 5033110940, 4871147567, 4716051202, 4567443623, 4424972741, 4288310366, 4157150201, 4031206054, 3910210217, 3793912015, 3682076488, 3574483195, 3470925133, 3371207750, 3275148046, 3182573751, 3093322573, 3007241510, 2924186217, 2844020424, 2766615401, 2691849464, 2619607520, 2549780642, 2482265687, 2416964926, 2353785714, 2292640180, 2233444932, 2176120798, 2120592564, 2066788753, 2014641398, 1964085843, 1915060555, 1867506945, 1821369202, 1776594140, 1733131050, 1690931567, 1649949541, 1610140918, 1571463626, 1533877472, 1497344041, 1461826605, 1427290031, 1393700705, 1361026449, 1329236450, 1298301191, 1268192385, 1238882917, 1210346781, 1182559030, 1155495723, 1129133873, 1103451410, 1078427125, 1054040640, 1030272364, 1007103455, 984515790, 962491925, 941015073, 920069064, 899638327, 879707855, 860263185, 841290371, 822775966, 804706994, 787070934, 769855698, 753049616, 736641415, 720620202, 704975452, 689696989, 674774975, 660199892, 645962532, 632053986, 618465628, 605189106, 592216333, 579539473, 567150934, 555043357, 543209611, 531642777, 520336147, 509283213, 498477661, 487913362, 477584368, 467484901, 457609353, 447952274, 438508372, 429272503, 420239667, 411405005, 402763792, 394311434, 386043461, 377955527, 370043403, 362302973, 354730232, 347321279, 340072320, 332979658, 326039694, 319248922, 312603926, 306101379, 299738038, 293510745, 287416419]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 938).prefactor = (1178182789898137/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 938).cutoff/(generalMeanRows 938).c)).2 =
    (379540768675747/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 938).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 938).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 938).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 938

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 938).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 938).criticalRate j.val*(generalMeanRows 938).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 938).c*(generalMeanRows 938).criticalPoint j.val)).2-
      (generalMeanRows 938).J/2-(generalMeanRows 938).error (generalMeanGrid j.val)+
      (generalMeanRows 938).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 938).c)).2-
      (generalMeanRows 938).J/2-(generalMeanRows 938).error 4 := by
  have he : (generalMeanRows 938).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 938) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 938)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0938

/-! Kernel-checked entropy margins for general spectral rectangle 939. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0939
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5266247272, 5092661174, 4926566271, 4767543816, 4615204510, 4469185915, 4329150166, 4194781913, 4065786473, 3941888176, 3822828865, 3708366544, 3598274150, 3492338445, 3390358993, 3292147245, 3197525688, 3106327078, 3018393725, 2933576851, 2851735986, 2772738418, 2696458689, 2622778124, 2551584399, 2482771138, 2416237544, 2351888056, 2289632024, 2229383417, 2171060544, 2114585799, 2059885420, 2006889262, 1955530596, 1905745907, 1857474716, 1810659408, 1765245073, 1721179357, 1678412321, 1636896312, 1596585838, 1557437450, 1519409641, 1482462737, 1446558802, 1411661553, 1377736269, 1344749712, 1312670057, 1281466814, 1251110766, 1221573902, 1192829361, 1164851376, 1137615216, 1111097142, 1085274354, 1060124952, 1035627887, 1011762928, 988510618, 965852242, 943769790, 922245928, 901263965, 880807825, 860862020, 841411622, 822442241, 803939999, 785891509, 768283856, 751104571, 734341618, 717983373, 702018607, 686436469, 671226473, 656378479, 641882683, 627729600, 613910054, 600415163, 587236331, 574365233, 561793807, 549514242, 537518970, 525800658, 514352194, 503166684, 492237441, 481557979, 471122006, 460923412, 450956271, 441214826, 431693490, 422386833, 413289584, 404396619, 395702959, 387203767, 378894338, 370770098, 362826601, 355059520, 347464647, 340037890, 332775263, 325672891, 318726999, 311933914, 305290059, 298791951, 292436197, 286219494, 280138622, 274190446]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 939).prefactor = (4845840348831359/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 939).cutoff/(generalMeanRows 939).c)).2 =
    (372896225957081/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 939).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 939).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 939).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 939

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 939).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 939).criticalRate j.val*(generalMeanRows 939).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 939).c*(generalMeanRows 939).criticalPoint j.val)).2-
      (generalMeanRows 939).J/2-(generalMeanRows 939).error (generalMeanGrid j.val)+
      (generalMeanRows 939).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 939).c)).2-
      (generalMeanRows 939).J/2-(generalMeanRows 939).error 4 := by
  have he : (generalMeanRows 939).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 939) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 939)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0939

/-! Kernel-checked entropy margins for general spectral rectangle 940. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0940
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5331267827, 5153251066, 4982948770, 4819929943, 4663793857, 4514167413, 4370702770, 4233075241, 4100981393, 3974137343, 3852277222, 3735151780, 3622527130, 3514183600, 3409914693, 3309526138, 3212835018, 3119668983, 3029865516, 2943271265, 2859741432, 2779139206, 2701335239, 2626207167, 2553639162, 2483521525, 2415750297, 2350226913, 2286857865, 2225554403, 2166232249, 2108811330, 2053215536, 1999372484, 1947213311, 1896672466, 1847687527, 1800199027, 1754150285, 1709487257, 1666158390, 1624114485, 1583308577, 1543695807, 1505233318, 1467880146, 1431597121, 1396346777, 1362093262, 1328802256, 1296440896, 1264977697, 1234382491, 1204626355, 1175681555, 1147521483, 1120120607, 1093454415, 1067499371, 1042232864, 1017633167, 993679395, 970351466, 947630064, 925496604, 903933199, 882922625, 862448298, 842494240, 823045053, 804085896, 785602458, 767580937, 750008016, 732870845, 716157019, 699854560, 683951898, 668437858, 653301639, 638532801, 624121249, 610057222, 596331277, 582934276, 569857377, 557092019, 544629913, 532463031, 520583596, 508984073, 497657159, 486595774, 475793055, 465242345, 454937188, 444871319, 435038660, 425433311, 416049546, 406881804, 397924685, 389172944, 380621487, 372265363, 364099761, 356120005, 348321550, 340699976, 333250986, 325970399, 318854151, 311898285, 305098953, 298452410, 291955010, 285603206, 279393542, 273322656, 267387272, 261584200]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 940).prefactor = (2491354576694363/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 940).cutoff/(generalMeanRows 940).c)).2 =
    (36629554192573/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 940).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 940).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 940).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 940

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 940).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 940).criticalRate j.val*(generalMeanRows 940).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 940).c*(generalMeanRows 940).criticalPoint j.val)).2-
      (generalMeanRows 940).J/2-(generalMeanRows 940).error (generalMeanGrid j.val)+
      (generalMeanRows 940).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 940).c)).2-
      (generalMeanRows 940).J/2-(generalMeanRows 940).error 4 := by
  have he : (generalMeanRows 940).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 940) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 940)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0940

/-! Kernel-checked entropy margins for general spectral rectangle 941. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0941
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5665815556, 5483954904, 5309879764, 5143154324, 4983373483, 4830160164, 4683162911, 4542053748, 4406526253, 4276293822, 4151088110, 4030657618, 3914766413, 3803192966, 3695729090, 3592178982, 3492358337, 3396093542, 3303220940, 3213586148, 3127043434, 3043455146, 2962691176, 2884628478, 2809150610, 2736147322, 2665514163, 2597152126, 2530967313, 2466870624, 2404777470, 2344607506, 2286284378, 2229735495, 2174891805, 2121687597, 2070060309, 2019950350, 1971300938, 1924057937, 1878169720, 1833587025, 1790262831, 1748152237, 1707212348, 1667402170, 1628682509, 1591015878, 1554366409, 1518699770, 1483983084, 1450184861, 1417274922, 1385224336, 1354005360, 1323591379, 1293956851, 1265077253, 1236929036, 1209489576, 1182737128, 1156650790, 1131210459, 1106396793, 1082191182, 1058575707, 1035533115, 1013046782, 991100693, 969679408, 948768039, 928352226, 908418115, 888952334, 869941973, 851374565, 833238066, 815520838, 798211634, 781299576, 764774146, 748625170, 732842802, 717417509, 702340067, 687601538, 673193266, 659106866, 645334206, 631867409, 618698833, 605821066, 593226921, 580909420, 568861794, 557077469, 545550063, 534273378, 523241393, 512448258, 501888288, 491555957, 481445892, 471552870, 461871809, 452397769, 443125941, 434051646, 425170331, 416477562, 407969024, 399640515, 391487942, 383507319, 375694762, 368046487, 360558807, 353228128, 346050947, 339023848, 332143501]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 941).prefactor = (1263146619809949/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 941).cutoff/(generalMeanRows 941).c)).2 =
    (386229756826547/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 941).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 941).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 941).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 941

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 941).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 941).criticalRate j.val*(generalMeanRows 941).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 941).c*(generalMeanRows 941).criticalPoint j.val)).2-
      (generalMeanRows 941).J/2-(generalMeanRows 941).error (generalMeanGrid j.val)+
      (generalMeanRows 941).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 941).c)).2-
      (generalMeanRows 941).J/2-(generalMeanRows 941).error 4 := by
  have he : (generalMeanRows 941).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 941) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 941)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0941

/-! Kernel-checked entropy margins for general spectral rectangle 942. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0942
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7449035802, 7240386582, 7039774592, 6846784526, 6661029581, 6482148887, 6309805229, 6143683021, 5983486501, 5828938120, 5679777088, 5535758077, 5396650040, 5262235154, 5132307853, 5006673955, 4885149866, 4767561853, 4653745378, 4543544492, 4436811277, 4333405331, 4233193295, 4136048422, 4041850170, 3950483830, 3861840185, 3775815186, 3692309657, 3611229020, 3532483035, 3455985563, 3381654340, 3309410770, 3239179730, 3170889384, 3104471017, 3039858867, 2976989982, 2915804072, 2856243382, 2798252561, 2741778547, 2686770454, 2633179470, 2580958757, 2530063356, 2480450100, 2432077532, 2384905822, 2338896697, 2294013369, 2250220466, 2207483970, 2165771157, 2125050539, 2085291811, 2046465797, 2008544406, 1971500579, 1935308249, 1899942299, 1865378520, 1831593572, 1798564952, 1766270956, 1734690646, 1703803819, 1673590978, 1644033304, 1615112625, 1586811393, 1559112661, 1532000052, 1505457745, 1479470447, 1454023376, 1429102240, 1404693216, 1380782935, 1357358462, 1334407283, 1311917285, 1289876743, 1268274304, 1247098977, 1226340113, 1205987399, 1186030840, 1166460752, 1147267747, 1128442724, 1109976859, 1091861593, 1074088626, 1056649904, 1039537611, 1022744163, 1006262199, 990084570, 974204335, 958614753, 943309277, 928281544, 913525373, 899034754, 884803848, 870826976, 857098618, 843613401, 830366104, 817351644, 804565075, 792001585, 779656490, 767525228, 755603359, 743886558, 732370613, 721051420, 709924980]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 942).prefactor = (4869665035030099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 942).cutoff/(generalMeanRows 942).c)).2 =
    (7834091227081/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 942).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 942).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 942).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 942

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 942).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 942).criticalRate j.val*(generalMeanRows 942).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 942).c*(generalMeanRows 942).criticalPoint j.val)).2-
      (generalMeanRows 942).J/2-(generalMeanRows 942).error (generalMeanGrid j.val)+
      (generalMeanRows 942).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 942).c)).2-
      (generalMeanRows 942).J/2-(generalMeanRows 942).error 4 := by
  have he : (generalMeanRows 942).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 942) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 942)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0942

/-! Kernel-checked entropy margins for general spectral rectangle 943. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0943
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7153036043, 6944941312, 6744961654, 6552676840, 6367695431, 6189652192, 6018205799, 5853036797, 5693845789, 5540351800, 5392290820, 5249414488, 5111488907, 4978293570, 4849620386, 4725272799, 4605064978, 4488821085, 4376374604, 4267567721, 4162250762, 4060281673, 3961525541, 3865854152, 3773145584, 3683283831, 3596158448, 3511664233, 3429700924, 3350172917, 3272989005, 3198062139, 3125309195, 3054650768, 2986010969, 2919317241, 2854500186, 2791493402, 2730233328, 2670659102, 2612712425, 2556337435, 2501480586, 2448090535, 2396118037, 2345515843, 2296238607, 2248242796, 2201486603, 2155929870, 2111534013, 2068261946, 2026078017, 1984947942, 1944838744, 1905718694, 1867557260, 1830325049, 1793993763, 1758536149, 1723925951, 1690137876, 1657147544, 1624931457, 1593466956, 1562732191, 1532706085, 1503368301, 1474699215, 1446679886, 1419292027, 1392517978, 1366340686, 1340743674, 1315711022, 1291227346, 1267277775, 1243847930, 1220923909, 1198492263, 1176539985, 1155054488, 1134023591, 1113435503, 1093278809, 1073542458, 1054215743, 1035288296, 1016750070, 998591330, 980802640, 963374853, 946299102, 929566786, 913169564, 897099343, 881348273, 865908735, 850773334, 835934890, 821386433, 807121195, 793132600, 779414263, 765959976, 752763711, 739819607, 727121964, 714665245, 702444062, 690453177, 678687494, 667142054, 655812033, 644692737, 633779594, 623068158, 612554095, 602233188, 592101328, 582154514]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 943).prefactor = (307519965359859/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 943).cutoff/(generalMeanRows 943).c)).2 =
    (302417771105549/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 943).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 943).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 943).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 943

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 943).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 943).criticalRate j.val*(generalMeanRows 943).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 943).c*(generalMeanRows 943).criticalPoint j.val)).2-
      (generalMeanRows 943).J/2-(generalMeanRows 943).error (generalMeanGrid j.val)+
      (generalMeanRows 943).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 943).c)).2-
      (generalMeanRows 943).J/2-(generalMeanRows 943).error 4 := by
  have he : (generalMeanRows 943).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 943) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 943)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0943

/-! Kernel-checked entropy margins for general spectral rectangle 944. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0944
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6885395007, 6688158555, 6498686607, 6316571783, 6141434687, 5972921408, 5810701302, 5654465024, 5503922759, 5358802650, 5218849375, 5083822874, 4953497190, 4827659431, 4706108817, 4588655820, 4475121380, 4365336184, 4259140014, 4156381140, 4056915773, 3960607551, 3867327074, 3776951472, 3689364002, 3604453682, 3522114947, 3442247330, 3364755168, 3289547327, 3216536944, 3145641192, 3076781054, 3009881116, 2944869376, 2881677053, 2820238428, 2760490674, 2702373711, 2645830066, 2590804735, 2537245066, 2485100633, 2434323135, 2384866282, 2336685706, 2289738861, 2243984941, 2199384793, 2155900842, 2113497014, 2072138669, 2031792535, 1992426640, 1954010261, 1916513860, 1879909033, 1844168463, 1809265866, 1775175949, 1741874365, 1709337672, 1677543296, 1646469489, 1616095297, 1586400526, 1557365709, 1528972074, 1501201519, 1474036580, 1447460405, 1421456731, 1396009859, 1371104629, 1346726402, 1322861034, 1299494862, 1276614679, 1254207720, 1232261642, 1210764510, 1189704776, 1169071273, 1148853189, 1129040063, 1109621765, 1090588488, 1071930732, 1053639295, 1035705259, 1018119984, 1000875094, 983962466, 967374226, 951102734, 935140581, 919480575, 904115737, 889039294, 874244666, 859725468, 845475495, 831488720, 817759286, 804281501, 791049834, 778058904, 765303482, 752778480, 740478949, 728400075, 716537170, 704885676, 693441151, 682199273, 671155833, 660306729, 649647968, 639175657, 628886002, 618775309]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 944).prefactor = (953346161314799/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 944).cutoff/(generalMeanRows 944).c)).2 =
    (331815542678501/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 944).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 944).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 944).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 944

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 944).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 944).criticalRate j.val*(generalMeanRows 944).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 944).c*(generalMeanRows 944).criticalPoint j.val)).2-
      (generalMeanRows 944).J/2-(generalMeanRows 944).error (generalMeanGrid j.val)+
      (generalMeanRows 944).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 944).c)).2-
      (generalMeanRows 944).J/2-(generalMeanRows 944).error 4 := by
  have he : (generalMeanRows 944).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 944) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 944)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0944

/-! Kernel-checked entropy margins for general spectral rectangle 945. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0945
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6635460750, 6440112066, 6252538483, 6072330447, 5899106532, 5732510938, 5572211267, 5417896547, 5269275464, 5126074775, 4988037887, 4854923570, 4726504802, 4602567713, 4482910637, 4367343241, 4255685735, 4147768152, 4043429682, 3942518070, 3844889054, 3750405858, 3658938716, 3570364438, 3484566006, 3401432198, 3320857250, 3242740526, 3166986228, 3093503112, 3022204233, 2953006706, 2885831476, 2820603113, 2757249613, 2695702215, 2635895228, 2577765872, 2521254123, 2466302573, 2412856298, 2360862727, 2310271530, 2261034502, 2213105458, 2166440140, 2120996114, 2076732690, 2033610836, 1991593096, 1950643523, 1910727600, 1871812179, 1833865416, 1796856713, 1760756658, 1725536974, 1691170466, 1657630975, 1624893331, 1592933307, 1561727581, 1531253697, 1501490023, 1472415720, 1444010706, 1416255624, 1389131810, 1362621268, 1336706637, 1311371168, 1286598697, 1262373621, 1238680876, 1215505914, 1192834683, 1170653607, 1148949564, 1127709875, 1106922276, 1086574913, 1066656315, 1047155390, 1028061400, 1009363954, 991052993, 973118777, 955551871, 938343138, 921483723, 904965045, 888778788, 872916887, 857371524, 842135114, 827200300, 812559943, 798207116, 784135092, 770337343, 756807529, 743539491, 730527248, 717764988, 705247061, 692967977, 680922400, 669105138, 657511144, 646135510, 634973457, 624020339, 613271631, 602722932, 592369952, 582208520, 572234568, 562444138, 552833372, 543398510, 534135889]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 945).prefactor = (4786788684913803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 945).cutoff/(generalMeanRows 945).c)).2 =
    (16391969714943/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 945).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 945).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 945).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 945

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 945).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 945).criticalRate j.val*(generalMeanRows 945).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 945).c*(generalMeanRows 945).criticalPoint j.val)).2-
      (generalMeanRows 945).J/2-(generalMeanRows 945).error (generalMeanGrid j.val)+
      (generalMeanRows 945).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 945).c)).2-
      (generalMeanRows 945).J/2-(generalMeanRows 945).error 4 := by
  have he : (generalMeanRows 945).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 945) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 945)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0945

/-! Kernel-checked entropy margins for general spectral rectangle 946. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0946
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6238810527, 6046463424, 5861897611, 5684701903, 5514493320, 5350914586, 5193631909, 5042333005, 4896725325, 4756534469, 4621502762, 4491387967, 4365962119, 4245010477, 4128330563, 4015731294, 3907032186, 3802062629, 3700661222, 3602675165, 3507959698, 3416377587, 3327798644, 3242099296, 3159162173, 3078875737, 3001133932, 2925835861, 2852885486, 2782191350, 2713666316, 2647227324, 2582795166, 2520294275, 2459652525, 2400801046, 2343674056, 2288208691, 2234344858, 2182025088, 2131194406, 2081800201, 2033792107, 1987121891, 1941743352, 1897612213, 1854686035, 1812924123, 1772287444, 1732738551, 1694241503, 1656761795, 1620266295, 1584723178, 1550101864, 1516372966, 1483508231, 1451480491, 1420263616, 1389832465, 1360162843, 1331231461, 1303015896, 1275494552, 1248646624, 1222452068, 1196891564, 1171946487, 1147598878, 1123831417, 1100627395, 1077970688, 1055845734, 1034237512, 1013131516, 992513735, 972370638, 952689146, 933456623, 914660851, 896290020, 878332705, 860777860, 843614792, 826833159, 810422948, 794374466, 778678328, 763325444, 748307009, 733614493, 719239628, 705174402, 691411047, 677942030, 664760046, 651858010, 639229048, 626866487, 614763855, 602914865, 591313417, 579953583, 568829609, 557935904, 547267035, 536817725, 526582842, 516557399, 506736546, 497115569, 487689880, 478455020, 469406647, 460540538, 451852584, 443338782, 434995239, 426818163, 418803859, 410948733]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 946).prefactor = (4795360769954721/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 946).cutoff/(generalMeanRows 946).c)).2 =
    (156954775144341/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 946).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 946).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 946).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 946

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 946).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 946).criticalRate j.val*(generalMeanRows 946).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 946).c*(generalMeanRows 946).criticalPoint j.val)).2-
      (generalMeanRows 946).J/2-(generalMeanRows 946).error (generalMeanGrid j.val)+
      (generalMeanRows 946).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 946).c)).2-
      (generalMeanRows 946).J/2-(generalMeanRows 946).error 4 := by
  have he : (generalMeanRows 946).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 946) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 946)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0946

/-! Kernel-checked entropy margins for general spectral rectangle 947. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0947
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5816455007, 5628128498, 5447570747, 5274369457, 5108140572, 4948525787, 4795190331, 4647820990, 4506124342, 4369825167, 4238665025, 4112400966, 3990804365, 3873659871, 3760764446, 3651926492, 3546965055, 3445709100, 3347996837, 3253675120, 3162598874, 3074630585, 2989639821, 2907502789, 2828101930, 2751325543, 2677067433, 2605226585, 2535706866, 2468416745, 2403269024, 2340180605, 2279072254, 2219868392, 2162496895, 2106888911, 2052978681, 2000703378, 1950002955, 1900820000, 1853099599, 1806789211, 1761838548, 1718199462, 1675825838, 1634673495, 1594700093, 1555865039, 1518129409, 1481455864, 1445808577, 1411153163, 1377456606, 1344687203, 1312814499, 1281809231, 1251643275, 1222289590, 1193722177, 1165916026, 1138847076, 1112492169, 1086829018, 1061836160, 1037492929, 1013779413, 990676432, 968165496, 946228785, 924849117, 904009920, 883695208, 863889559, 844578090, 825746434, 807380719, 789467553, 771993996, 754947552, 738316142, 722088094, 706252124, 690797324, 675713143, 660989375, 646616148, 632583908, 618883410, 605505703, 592442120, 579684272, 567224029, 555053519, 543165111, 531551414, 520205260, 509119704, 498288009, 487703643, 477360271, 467251745, 457372103, 447715557, 438276490, 429049450, 420029141, 411210424, 402588306, 394157936, 385914604, 377853730, 369970866, 362261688, 354721992, 347347691, 340134812, 333079490, 326177966, 319426584, 312821786, 306360112]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 947).prefactor = (1198333471442417/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 947).cutoff/(generalMeanRows 947).c)).2 =
    (59675472313709/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 947).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 947).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 947).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 947

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 947).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 947).criticalRate j.val*(generalMeanRows 947).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 947).c*(generalMeanRows 947).criticalPoint j.val)).2-
      (generalMeanRows 947).J/2-(generalMeanRows 947).error (generalMeanGrid j.val)+
      (generalMeanRows 947).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 947).c)).2-
      (generalMeanRows 947).J/2-(generalMeanRows 947).error 4 := by
  have he : (generalMeanRows 947).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 947) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 947)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0947

/-! Kernel-checked entropy margins for general spectral rectangle 948. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0948
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5542733579, 5358351803, 5181686853, 5012326642, 4849887330, 4694010835, 4544362630, 4400629762, 4262519093, 4129755714, 4002081521, 3879253923, 3761044683, 3647238860, 3537633846, 3432038501, 3330272344, 3232164833, 3137554690, 3046289293, 2958224107, 2873222170, 2791153610, 2711895207, 2635329981, 2561346814, 2489840100, 2420709419, 2353859233, 2289198607, 2226640941, 2166103734, 2107508346, 2050779791, 1995846536, 1942640312, 1891095945, 1841151183, 1792746551, 1745825201, 1700332779, 1656217296, 1613429010, 1571920310, 1531645614, 1492561261, 1454625428, 1417798029, 1382040637, 1347316407, 1313589992, 1280827480, 1248996323, 1218065275, 1188004329, 1158784664, 1130378586, 1102759480, 1075901763, 1049780833, 1024373028, 999655583, 975606595, 952204978, 929430434, 907263414, 885685091, 864677323, 844222630, 824304163, 804905676, 786011504, 767606537, 749676199, 732206423, 715183634, 698594726, 682427044, 666668366, 651306887, 636331201, 621730285, 607493485, 593610501, 580071374, 566866472, 553986479, 541422379, 529165449, 517207248, 505539603, 494154599, 483044575, 472202109, 461620010, 451291311, 441209263, 431367322, 421759144, 412378580, 403219666, 394276617, 385543823, 377015840, 368687385, 360553334, 352608709, 344848680, 337268557, 329863786, 322629942, 315562731, 308657976, 301911622, 295319729, 288878465, 282584107, 276433035, 270421729, 264546768, 258804823]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 948).prefactor = (239076994046497/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 948).cutoff/(generalMeanRows 948).c)).2 =
    (147712367807289/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 948).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 948).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 948).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 948

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 948).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 948).criticalRate j.val*(generalMeanRows 948).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 948).c*(generalMeanRows 948).criticalPoint j.val)).2-
      (generalMeanRows 948).J/2-(generalMeanRows 948).error (generalMeanGrid j.val)+
      (generalMeanRows 948).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 948).c)).2-
      (generalMeanRows 948).J/2-(generalMeanRows 948).error 4 := by
  have he : (generalMeanRows 948).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 948) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 948)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0948

/-! Kernel-checked entropy margins for general spectral rectangle 949. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0949
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5615581565, 5441651993, 5274933816, 5115034797, 4961589930, 4814259041, 4672724661, 4536690124, 4405877862, 4280027876, 4158896355, 4042254432, 3929887055, 3821591967, 3717178772, 3616468091, 3519290785, 3425487248, 3334906760, 3247406890, 3162852949, 3081117484, 3002079817, 2925625614, 2851646487, 2780039628, 2710707467, 2643557358, 2578501285, 2515455587, 2454340707, 2395080949, 2337604267, 2281842049, 2227728930, 2175202609, 2124203682, 2074675484, 2026563941, 1979817427, 1934386642, 1890224483, 1847285930, 1805527940, 1764909344, 1725390750, 1686934458, 1649504367, 1613065900, 1577585931, 1543032705, 1509375779, 1476585956, 1444635222, 1413496692, 1383144557, 1353554030, 1324701301, 1296563491, 1269118605, 1242345497, 1216223827, 1190734027, 1165857263, 1141575406, 1117870997, 1094727218, 1072127866, 1050057323, 1028500534, 1007442979, 986870652, 966770039, 947128096, 927932232, 909170285, 890830510, 872901558, 855372460, 838232612, 821471761, 805079991, 789047706, 773365622, 758024751, 743016394, 728332122, 713963774, 699903441, 686143458, 672676396, 659495052, 646592439, 633961780, 621596500, 609490219, 597636744, 586030059, 574664328, 563533876, 552633195, 541956930, 531499877, 521256979, 511223316, 501394107, 491764699, 482330568, 473087309, 464030637, 455156381, 446460481, 437938982, 429588035, 421403888, 413382887, 405521473, 397816175, 390263614, 382860492, 375603596]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 949).prefactor = (915778643706863/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 949).cutoff/(generalMeanRows 949).c)).2 =
    (71715289339683/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 949).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 949).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 949).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 949

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 949).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 949).criticalRate j.val*(generalMeanRows 949).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 949).c*(generalMeanRows 949).criticalPoint j.val)).2-
      (generalMeanRows 949).J/2-(generalMeanRows 949).error (generalMeanGrid j.val)+
      (generalMeanRows 949).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 949).c)).2-
      (generalMeanRows 949).J/2-(generalMeanRows 949).error 4 := by
  have he : (generalMeanRows 949).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 949) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 949)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0949

/-! Kernel-checked entropy margins for general spectral rectangle 950. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0950
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5471028831, 5300797823, 5137672611, 4981263730, 4831208853, 4687170420, 4548833509, 4415903946, 4288106599, 4165183858, 4046894252, 3933011211, 3823321938, 3717626386, 3615736329, 3517474517, 3422673898, 3331176915, 3242834855, 3157507253, 3075061345, 2995371564, 2918319078, 2843791356, 2771681772, 2701889243, 2634317881, 2568876684, 2505479235, 2444043438, 2384491257, 2326748482, 2270744509, 2216412135, 2163687361, 2112509219, 2062819598, 2014563090, 1967686841, 1922140414, 1877875658, 1834846587, 1793009264, 1752321699, 1712743740, 1674236983, 1636764682, 1600291663, 1564784248, 1530210176, 1496538533, 1463739688, 1431785230, 1400647906, 1370301564, 1340721105, 1311882429, 1283762389, 1256338743, 1229590118, 1203495963, 1178036514, 1153192760, 1128946402, 1105279829, 1082176082, 1059618824, 1037592316, 1016081390, 995071421, 974548304, 954498436, 934908688, 915766391, 897059310, 878775630, 860903940, 843433209, 826352780, 809652345, 793321939, 777351919, 761732958, 746456027, 731512384, 716893565, 702591374, 688597866, 674905345, 661506351, 648393649, 635560225, 622999275, 610704197, 598668585, 586886219, 575351064, 564057255, 552999098, 542171061, 531567769, 521183995, 511014662, 501054832, 491299701, 481744598, 472384980, 463216424, 454234627, 445435399, 436814663, 428368447, 420092884, 411984206, 404038744, 396252920, 388623250, 381146337, 373818869, 366637617, 359599434]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 950).prefactor = (1137639340474171/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 950).cutoff/(generalMeanRows 950).c)).2 =
    (46065371366913/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 950).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 950).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 950).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 950

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 950).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 950).criticalRate j.val*(generalMeanRows 950).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 950).c*(generalMeanRows 950).criticalPoint j.val)).2-
      (generalMeanRows 950).J/2-(generalMeanRows 950).error (generalMeanGrid j.val)+
      (generalMeanRows 950).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 950).c)).2-
      (generalMeanRows 950).J/2-(generalMeanRows 950).error 4 := by
  have he : (generalMeanRows 950).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 950) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 950)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0950

/-! Kernel-checked entropy margins for general spectral rectangle 951. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0951
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5245925999, 5079950985, 4920973020, 4768605868, 4622490306, 4482291762, 4347698204, 4218418251, 4094179482, 3974726915, 3859821636, 3749239561, 3642770308, 3540216185, 3441391258, 3346120508, 3254239055, 3165591458, 3080031063, 2997419411, 2917625690, 2840526232, 2766004050, 2693948410, 2624254435, 2556822735, 2491559074, 2428374049, 2367182799, 2307904736, 2250463288, 2194785664, 2140802639, 2088448341, 2037660066, 1988378096, 1940545535, 1894108146, 1849014213, 1805214396, 1762661609, 1721310892, 1681119304, 1642045813, 1604051195, 1567097944, 1531150179, 1496173562, 1462135222, 1429003676, 1396748765, 1365341582, 1334754415, 1304960687, 1275934898, 1247652578, 1220090231, 1193225294, 1167036091, 1141501789, 1116602361, 1092318549, 1068631827, 1045524366, 1022979006, 1000979223, 979509101, 958553305, 938097057, 918126108, 898626716, 879585627, 860990050, 842827638, 825086471, 807755038, 790822216, 774277259, 758109777, 742309727, 726867396, 711773385, 697018601, 682594244, 668491793, 654702995, 641219859, 628034640, 615139833, 602528163, 590192577, 578126234, 566322498, 554774931, 543477285, 532423494, 521607670, 511024095, 500667215, 490531632, 480612104, 470903534, 461400968, 452099590, 442994715, 434081788, 425356375, 416814166, 408450962, 400262679, 392245340, 384395073, 376708107, 369180769, 361809482, 354590760, 347521206, 340597511, 333816446, 327174868, 320669709]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 951).prefactor = (1128839811126191/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 951).cutoff/(generalMeanRows 951).c)).2 =
    (186380540845187/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 951).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 951).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 951).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 951

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 951).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 951).criticalRate j.val*(generalMeanRows 951).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 951).c*(generalMeanRows 951).criticalPoint j.val)).2-
      (generalMeanRows 951).J/2-(generalMeanRows 951).error (generalMeanGrid j.val)+
      (generalMeanRows 951).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 951).c)).2-
      (generalMeanRows 951).J/2-(generalMeanRows 951).error 4 := by
  have he : (generalMeanRows 951).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 951) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 951)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0951

/-! Kernel-checked entropy margins for general spectral rectangle 952. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0952
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5081888866, 4912499886, 4750367350, 4595091700, 4446301208, 4303649536, 4166813569, 4035491473, 3909400960, 3788277715, 3671873997, 3559957353, 3452309473, 3348725135, 3249011256, 3152986019, 3060478081, 2971325844, 2885376793, 2802486880, 2722519964, 2645347291, 2570847022, 2498903785, 2429408271, 2362256858, 2297351258, 2234598193, 2173909096, 2115199828, 2058390418, 2003404823, 1950170696, 1898619178, 1848684700, 1800304799, 1753419946, 1707973380, 1663910963, 1621181034, 1579734277, 1539523597, 1500504000, 1462632488, 1425867949, 1390171063, 1355504213, 1321831392, 1289118127, 1257331401, 1226439578, 1196412339, 1167220615, 1138836526, 1111233324, 1084385341, 1058267934, 1032857437, 1008131117, 984067131, 960644482, 937842980, 915643209, 894026488, 872974839, 852470956, 832498176, 813040447, 794082304, 775608846, 757605703, 740059024, 722955446, 706282077, 690026478, 674176639, 658720966, 643648261, 628947707, 614608851, 600621591, 586976161, 573663118, 560673327, 547997954, 535628447, 523556532, 511774199, 500273690, 489047492, 478088329, 467389150, 456943121, 446743620, 436784224, 427058707, 417561031, 408285337, 399225940, 390377325, 381734139, 373291183, 365043412, 356985925, 349113962, 341422900, 333908246, 326565634, 319390821, 312379683, 305528209, 298832502, 292288768, 285893320, 279642570, 273533028, 267561297, 261724072, 256018136, 250440357, 244987687]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 952).prefactor = (2326434335766609/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 952).cutoff/(generalMeanRows 952).c)).2 =
    (346092834608211/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 952).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 952).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 952).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 952

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 952).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 952).criticalRate j.val*(generalMeanRows 952).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 952).c*(generalMeanRows 952).criticalPoint j.val)).2-
      (generalMeanRows 952).J/2-(generalMeanRows 952).error (generalMeanGrid j.val)+
      (generalMeanRows 952).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 952).c)).2-
      (generalMeanRows 952).J/2-(generalMeanRows 952).error 4 := by
  have he : (generalMeanRows 952).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 952) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 952)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0952

/-! Kernel-checked entropy margins for general spectral rectangle 953. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0953
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5256976859, 5090409067, 4930902467, 4778064025, 4631528347, 4490955265, 4356027667, 4226449573, 4101944398, 3982253394, 3867134243, 3756359788, 3649716881, 3547005338, 3448036986, 3352634796, 3260632094, 3171871829, 3086205918, 3003494629, 2923606021, 2846415433, 2771805001, 2699663224, 2629884555, 2562369027, 2497021903, 2433753357, 2372478167, 2313115445, 2255588371, 2199823958, 2145752821, 2093308972, 2042429622, 1993055001, 1945128183, 1898594930, 1853403542, 1809504714, 1766851411, 1725398737, 1685103826, 1645925730, 1607825321, 1570765190, 1534709561, 1499624206, 1465476364, 1432234667, 1399869070, 1368350782, 1337652206, 1307746879, 1278609413, 1250215448, 1222541598, 1195565407, 1169265299, 1143620543, 1118611209, 1094218131, 1070422871, 1047207689, 1024555505, 1002449873, 980874951, 959815475, 939256732, 919184536, 899585203, 880445534, 861752788, 843494666, 825659293, 808235195, 791211286, 774576855, 758321541, 742435327, 726908524, 711731754, 696895943, 682392304, 668212329, 654347776, 640790661, 627533243, 614568022, 601887722, 589485290, 577353882, 565486856, 553877768, 542520362, 531408563, 520536470, 509898353, 499488644, 489301930, 479332954, 469576600, 460027898, 450682010, 441534234, 432579992, 423814831, 415234416, 406834528, 398611059, 390560008, 382677480, 374959678, 367402906, 360003562, 352758133, 345663199, 338715424, 331911554, 325248420, 318722928]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 953).prefactor = (1151018293736541/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 953).cutoff/(generalMeanRows 953).c)).2 =
    (48124726017351/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 953).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 953).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 953).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 953

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 953).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 953).criticalRate j.val*(generalMeanRows 953).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 953).c*(generalMeanRows 953).criticalPoint j.val)).2-
      (generalMeanRows 953).J/2-(generalMeanRows 953).error (generalMeanGrid j.val)+
      (generalMeanRows 953).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 953).c)).2-
      (generalMeanRows 953).J/2-(generalMeanRows 953).error 4 := by
  have he : (generalMeanRows 953).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 953) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 953)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0953

/-! Kernel-checked entropy margins for general spectral rectangle 954. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0954
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5244255379, 5073619048, 4910274156, 4753815463, 4603866168, 4460075416, 4322116078, 4189682768, 4062490059, 3940270879, 3822775074, 3709768090, 3601029799, 3496353420, 3395544542, 3298420230, 3204808216, 3114546148, 3027480909, 2943467991, 2862370917, 2784060711, 2708415409, 2635319605, 2564664036, 2496345194, 2430264967, 2366330310, 2304452934, 2244549019, 2186538951, 2130347069, 2075901437, 2023133628, 1971978521, 1922374115, 1874261350, 1827583948, 1782288253, 1738323091, 1695639632, 1654191265, 1613933481, 1574823755, 1536821449, 1499887706, 1463985362, 1429078858, 1395134157, 1362118667, 1330001167, 1298751739, 1268341706, 1238743567, 1209930938, 1181878505, 1154561963, 1127957976, 1102044124, 1076798864, 1052201488, 1028232082, 1004871492, 982101287, 959903728, 938261734, 917158854, 896579240, 876507616, 856929259, 837829970, 819196052, 801014290, 783271928, 765956653, 749056573, 732560199, 716456433, 700734547, 685384168, 670395267, 655758142, 641463407, 627501976, 613865057, 600544135, 587530962, 574817550, 562396158, 550259284, 538399654, 526810216, 515484132, 504414765, 493595680, 483020628, 472683546, 462578545, 452699909, 443042085, 433599678, 424367449, 415340302, 406513288, 397881594, 389440541, 381185576, 373112274, 365216330, 357493552, 349939864, 342551298, 335323992, 328254184, 321338213, 314572513, 307953610, 301478123, 295142754, 288944292, 282879608]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 954).prefactor = (1184488337737983/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 954).cutoff/(generalMeanRows 954).c)).2 =
    (371796296280273/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 954).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 954).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 954).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 954

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 954).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 954).criticalRate j.val*(generalMeanRows 954).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 954).c*(generalMeanRows 954).criticalPoint j.val)).2-
      (generalMeanRows 954).J/2-(generalMeanRows 954).error (generalMeanGrid j.val)+
      (generalMeanRows 954).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 954).c)).2-
      (generalMeanRows 954).J/2-(generalMeanRows 954).error 4 := by
  have he : (generalMeanRows 954).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 954) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 954)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0954

/-! Kernel-checked entropy margins for general spectral rectangle 955. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0955
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5314001397, 5138845450, 4971205039, 4810662712, 4656830277, 4509346246, 4367873543, 4232097471, 4101723871, 3976477481, 3856100447, 3740350977, 3629002129, 3521840699, 3418666220, 3319290043, 3223534499, 3131232132, 3042224998, 2956364018, 2873508386, 2793525021, 2716288067, 2641678426, 2569583325, 2499895926, 2432514951, 2367344342, 2304292945, 2243274213, 2184205934, 2127009974, 2071612039, 2017941452, 1965930949, 1915516482, 1866637040, 1819234478, 1773253360, 1728640810, 1685346373, 1643321883, 1602521343, 1562900808, 1524418277, 1487033592, 1450708342, 1415405776, 1381090713, 1347729465, 1315289762, 1283740683, 1253052585, 1223197042, 1194146787, 1165875654, 1138358525, 1111571280, 1085490750, 1060094672, 1035361646, 1011271096, 987803230, 964939007, 942660099, 920948863, 899788305, 879162057, 859054345, 839449963, 820334253, 801693074, 783512784, 765780220, 748482675, 731607877, 715143977, 699079526, 683403459, 668105083, 653174058, 638600384, 624374387, 610486710, 596928292, 583690365, 570764437, 558142285, 545815943, 533777690, 522020045, 510535757, 499317792, 488359332, 477653761, 467194661, 456975805, 446991147, 437234820, 427701125, 418384528, 409279657, 400381287, 391684346, 383183904, 374875166, 366753474, 358814297, 351053229, 343465985, 336048396, 328796406, 321706069, 314773543, 307995090, 301367070, 294885940, 288548249, 282350637, 276289831, 270362642]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 955).prefactor = (975145316019403/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 955).cutoff/(generalMeanRows 955).c)).2 =
    (182630162650243/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 955).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 955).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 955).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 955

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 955).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 955).criticalRate j.val*(generalMeanRows 955).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 955).c*(generalMeanRows 955).criticalPoint j.val)).2-
      (generalMeanRows 955).J/2-(generalMeanRows 955).error (generalMeanGrid j.val)+
      (generalMeanRows 955).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 955).c)).2-
      (generalMeanRows 955).J/2-(generalMeanRows 955).error 4 := by
  have he : (generalMeanRows 955).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 955) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 955)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0955

/-! Kernel-checked entropy margins for general spectral rectangle 956. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0956
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5385004445, 5205238432, 5033218382, 4868514244, 4710726078, 4559481419, 4414432933, 4275256312, 4141648392, 4013325457, 3890021710, 3771487892, 3657490026, 3547808285, 3442235954, 3340578487, 3242652646, 3148285710, 3057314754, 2969585986, 2884954134, 2803281886, 2724439373, 2648303688, 2574758444, 2503693369, 2435003920, 2368590936, 2304360313, 2242222694, 2182093192, 2123891124, 2067539771, 2012966141, 1960100764, 1908877486, 1859233288, 1811108108, 1764444679, 1719188376, 1675287074, 1632691010, 1591352660, 1551226619, 1512269490, 1474439781, 1437697803, 1402005579, 1367326757, 1333626530, 1300871552, 1269029874, 1238070865, 1207965157, 1178684577, 1150202089, 1122491744, 1095528624, 1069288794, 1043749258, 1018887912, 994683502, 971115590, 948164511, 925811342, 904037864, 882826536, 862160460, 842023355, 822399530, 803273857, 784631748, 766459129, 748742424, 731468527, 714624786, 698198984, 682179320, 666554392, 651313181, 636445035, 621939655, 607787079, 593977673, 580502112, 567351371, 554516716, 541989686, 529762091, 517825993, 506173704, 494797771, 483690970, 472846298, 462256964, 451916379, 441818154, 431956088, 422324162, 412916536, 403727538, 394751662, 385983560, 377418037, 369050046, 360874682, 352887181, 345082909, 337457363, 330006164, 322725054, 315609893, 308656650, 301861408, 295220353, 288729775, 282386061, 276185696, 270125259, 264201416, 258410924]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 956).prefactor = (501750606706337/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 956).cutoff/(generalMeanRows 956).c)).2 =
    (358766795989939/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 956).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 956).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 956).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 956

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 956).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 956).criticalRate j.val*(generalMeanRows 956).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 956).c*(generalMeanRows 956).criticalPoint j.val)).2-
      (generalMeanRows 956).J/2-(generalMeanRows 956).error (generalMeanGrid j.val)+
      (generalMeanRows 956).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 956).c)).2-
      (generalMeanRows 956).J/2-(generalMeanRows 956).error 4 := by
  have he : (generalMeanRows 956).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 956) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 956)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0956

/-! Kernel-checked entropy margins for general spectral rectangle 957. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0957
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5541593038, 5356599675, 5179577516, 5010084006, 4847707575, 4692064927, 4542798629, 4399574941, 4262081885, 4130027494, 4003138243, 3881157622, 3763844853, 3650973716, 3542331486, 3437717959, 3336944568, 3239833569, 3146217302, 3055937501, 2968844670, 2884797505, 2803662359, 2725312751, 2649628912, 2576497361, 2505810516, 2437466334, 2371367972, 2307423475, 2245545489, 2185650985, 2127661011, 2071500454, 2017097824, 1964385043, 1913297259, 1863772664, 1815752327, 1769180032, 1724002140, 1680167440, 1637627027, 1596334176, 1556244227, 1517314482, 1479504096, 1442773991, 1407086757, 1372406573, 1338699125, 1305931534, 1274072280, 1243091139, 1212959119, 1183648399, 1155132275, 1127385104, 1100382256, 1074100065, 1048515784, 1023607543, 999354308, 975735844, 952732674, 930326054, 908497929, 887230912, 866508248, 846313788, 826631967, 807447770, 788746717, 770514834, 752738635, 735405101, 718501659, 702016165, 685936886, 670252481, 654951989, 640024812, 625460700, 611249735, 597382322, 583849176, 570641306, 557750008, 545166851, 532883668, 520892546, 509185816, 497756045, 486596025, 475698767, 465057492, 454665624, 444516782, 434604774, 424923586, 415467385, 406230503, 397207436, 388392839, 379781518, 371368426, 363148659, 355117450, 347270163, 339602294, 332109459, 324787398, 317631965, 310639127, 303804959, 297125643, 290597463, 284216800, 277980133, 271884033, 265925161]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 957).prefactor = (16135650963659/3125000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 957).cutoff/(generalMeanRows 957).c)).2 =
    (358766795989939/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 957).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 957).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 957).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 957

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 957).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 957).criticalRate j.val*(generalMeanRows 957).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 957).c*(generalMeanRows 957).criticalPoint j.val)).2-
      (generalMeanRows 957).J/2-(generalMeanRows 957).error (generalMeanGrid j.val)+
      (generalMeanRows 957).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 957).c)).2-
      (generalMeanRows 957).J/2-(generalMeanRows 957).error 4 := by
  have he : (generalMeanRows 957).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 957) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 957)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0957

/-! Kernel-checked entropy margins for general spectral rectangle 958. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0958
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7670921288, 7456215783, 7249694343, 7050937348, 6859553965, 6675179542, 6497473297, 6326116273, 6160809506, 6001272396, 5847241238, 5698467909, 5554718677, 5415773134, 5281423215, 5151472324, 5025734525, 4904033813, 4786203442, 4672085314, 4561529413, 4454393296, 4350541609, 4249845654, 4152182983, 4057437022, 3965496729, 3876256267, 3789614707, 3705475755, 3623747488, 3544342117, 3467175759, 3392168232, 3319242855, 3248326264, 3179348245, 3112241568, 3046941836, 2983387345, 2921518951, 2861279940, 2802615913, 2745474676, 2689806129, 2635562173, 2582696613, 2531165068, 2480924891, 2431935088, 2384156242, 2337550445, 2292081225, 2247713489, 2204413459, 2162148612, 2120887632, 2080600352, 2041257707, 2002831688, 1965295298, 1928622506, 1892788210, 1857768198, 1823539109, 1790078403, 1757364321, 1725375861, 1694092739, 1663495369, 1633564829, 1604282836, 1575631724, 1547594416, 1520154403, 1493295721, 1467002931, 1441261098, 1416055775, 1391372977, 1367199173, 1343521261, 1320326556, 1297602775, 1275338019, 1253520763, 1232139838, 1211184420, 1190644018, 1170508463, 1150767892, 1131412742, 1112433736, 1093821875, 1075568426, 1057664916, 1040103118, 1022875047, 1005972951, 989389298, 973116777, 957148281, 941476909, 926095951, 910998889, 896179384, 881631274, 867348567, 853325435, 839556210, 826035377, 812757570, 799717566, 786910283, 774330772, 761974215, 749835922, 737911323, 726195966, 714685517, 703375751]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 958).prefactor = (623590550165171/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 958).cutoff/(generalMeanRows 958).c)).2 =
    (373677546371/1250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 958).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 958).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 958).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 958

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 958).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 958).criticalRate j.val*(generalMeanRows 958).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 958).c*(generalMeanRows 958).criticalPoint j.val)).2-
      (generalMeanRows 958).J/2-(generalMeanRows 958).error (generalMeanGrid j.val)+
      (generalMeanRows 958).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 958).c)).2-
      (generalMeanRows 958).J/2-(generalMeanRows 958).error 4 := by
  have he : (generalMeanRows 958).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 958) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 958)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0958

/-! Kernel-checked entropy margins for general spectral rectangle 959. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0959
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7142904615, 6929698027, 6724774801, 6527710054, 6338107933, 6155599002, 5979837926, 5810501408, 5647286354, 5489908229, 5338099587, 5191608737, 5050198555, 4913645398, 4781738123, 4654277200, 4531073899, 4411949551, 4296734871, 4185269340, 4077400635, 3972984108, 3871882304, 3773964521, 3679106395, 3587189523, 3498101114, 3411733664, 3327984648, 3246756246, 3167955076, 3091491953, 3017281659, 2945242734, 2875297272, 2807370738, 2741391795, 2677292137, 2615006337, 2554471702, 2495628140, 2438418028, 2382786097, 2328679314, 2276046777, 2224839616, 2175010896, 2126515526, 2079310176, 2033353198, 1988604543, 1945025698, 1902579611, 1861230630, 1820944437, 1781687997, 1743429494, 1706138284, 1669784846, 1634340728, 1599778508, 1566071749, 1533194956, 1501123539, 1469833778, 1439302781, 1409508457, 1380429479, 1352045259, 1324335910, 1297282226, 1270865651, 1245068256, 1219872710, 1195262264, 1171220720, 1147732419, 1124782211, 1102355444, 1080437940, 1059015978, 1038076278, 1017605986, 997592653, 978024226, 958889030, 940175755, 921873442, 903971474, 886459557, 869327715, 852566274, 836165856, 820117362, 804411969, 789041116, 773996496, 759270048, 744853947, 730740598, 716922625, 703392868, 690144372, 677170380, 664464328, 652019841, 639830720, 627890942, 616194652, 604736159, 593509926, 582510571, 571732860, 561171700, 550822136, 540679347, 530738642, 520995456, 511445343, 502083976, 492907143]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 959).prefactor = (1258646067554269/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 959).cutoff/(generalMeanRows 959).c)).2 =
    (13660639556549/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 959).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 959).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 959).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 959

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 959).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 959).criticalRate j.val*(generalMeanRows 959).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 959).c*(generalMeanRows 959).criticalPoint j.val)).2-
      (generalMeanRows 959).J/2-(generalMeanRows 959).error (generalMeanGrid j.val)+
      (generalMeanRows 959).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 959).c)).2-
      (generalMeanRows 959).J/2-(generalMeanRows 959).error 4 := by
  have he : (generalMeanRows 959).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 959) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 959)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0959

/-! Kernel-checked entropy margins for general spectral rectangle 960. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0960
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7103293009, 6901601109, 6707763529, 6521371016, 6342042404, 6169422100, 6003177856, 5842998782, 5688593576, 5539688937, 5396028139, 5257369750, 5123486473, 4994164100, 4869200557, 4748405045, 4631597247, 4518606614, 4409271704, 4303439582, 4200965263, 4101711206, 4005546845, 3912348153, 3821997247, 3734382017, 3649395781, 3566936970, 3486908828, 3409219145, 3333779995, 3260507497, 3189321597, 3120145859, 3052907268, 2987536048, 2923965496, 2862131818, 2801973980, 2743433567, 2686454653, 2630983671, 2576969304, 2524362364, 2473115698, 2423184085, 2374524140, 2327094235, 2280854409, 2235766292, 2191793032, 2148899224, 2107050844, 2066215186, 2026360804, 1987457452, 1949476032, 1912388547, 1876168046, 1840788583, 1806225172, 1772453745, 1739451113, 1707194928, 1675663649, 1644836507, 1614693470, 1585215219, 1556383110, 1528179152, 1500585980, 1473586826, 1447165499, 1421306357, 1395994289, 1371214693, 1346953456, 1323196930, 1299931922, 1277145670, 1254825827, 1232960449, 1211537974, 1190547211, 1169977324, 1149817821, 1130058538, 1110689629, 1091701551, 1073085058, 1054831186, 1036931242, 1019376797, 1002159677, 985271948, 968705914, 952454104, 936509268, 920864365, 905512558, 890447205, 875661856, 861150242, 846906271, 832924021, 819197737, 805721820, 792490825, 779499458, 766742566, 754215136, 741912289, 729829274, 717961469, 706304369, 694853590, 683604861, 672554018, 661697008, 651029878, 640548776]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 960).prefactor = (4851681621371429/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 960).cutoff/(generalMeanRows 960).c)).2 =
    (323662084905763/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 960).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 960).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 960).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 960

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 960).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 960).criticalRate j.val*(generalMeanRows 960).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 960).c*(generalMeanRows 960).criticalPoint j.val)).2-
      (generalMeanRows 960).J/2-(generalMeanRows 960).error (generalMeanGrid j.val)+
      (generalMeanRows 960).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 960).c)).2-
      (generalMeanRows 960).J/2-(generalMeanRows 960).error 4 := by
  have he : (generalMeanRows 960).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 960) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 960)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0960

/-! Kernel-checked entropy margins for general spectral rectangle 961. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0961
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6684888017, 6485746176, 6294482416, 6110685256, 5933971402, 5763983238, 5600386593, 5442868756, 5291136704, 5144915508, 5003946910, 4867988035, 4736810228, 4610198006, 4487948098, 4369868581, 4255778086, 4145505078, 4038887193, 3935770631, 3836009600, 3739465805, 3646007974, 3555511423, 3467857654, 3382933982, 3300633191, 3220853213, 3143496827, 3068471388, 2995688566, 2925064104, 2856517598, 2789972284, 2725354841, 2662595212, 2601626429, 2542384452, 2484808018, 2428838501, 2374419773, 2321498086, 2270021948, 2219942013, 2171210979, 2123783484, 2077616016, 2032666827, 1988895841, 1946264587, 1904736113, 1864274926, 1824846916, 1786419300, 1748960556, 1712440371, 1676829586, 1642100141, 1608225033, 1575178263, 1542934798, 1511470525, 1480762215, 1450787481, 1421524747, 1392953210, 1365052811, 1337804198, 1311188705, 1285188316, 1259785645, 1234963904, 1210706882, 1186998924, 1163824904, 1141170206, 1119020706, 1097362747, 1076183126, 1055469076, 1035208244, 1015388682, 995998825, 977027480, 958463812, 940297329, 922517870, 905115591, 888080957, 871404726, 855077939, 839091915, 823438233, 808108728, 793095480, 778390805, 763987246, 749877567, 736054744, 722511957, 709242583, 696240191, 683498532, 671011537, 658773306, 646778106, 635020365, 623494663, 612195732, 601118448, 590257826, 579609017, 569167301, 558928087, 548886905, 539039403, 529381345, 519908603, 510617160, 501503101, 492562612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 961).prefactor = (4866174079650257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 961).cutoff/(generalMeanRows 961).c)).2 =
    (154572400178521/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 961).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 961).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 961).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 961

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 961).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 961).criticalRate j.val*(generalMeanRows 961).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 961).c*(generalMeanRows 961).criticalPoint j.val)).2-
      (generalMeanRows 961).J/2-(generalMeanRows 961).error (generalMeanGrid j.val)+
      (generalMeanRows 961).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 961).c)).2-
      (generalMeanRows 961).J/2-(generalMeanRows 961).error 4 := by
  have he : (generalMeanRows 961).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 961) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 961)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0961

/-! Kernel-checked entropy margins for general spectral rectangle 962. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0962
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6331405018, 6135543495, 5947551574, 5767016490, 5593553729, 5426804516, 5266433586, 5112127205, 4963591390, 4820550326, 4682744931, 4549931572, 4421880899, 4298376792, 4179215404, 4064204287, 3953161603, 3845915394, 3742302921, 3642170053, 3545370708, 3451766339, 3361225457, 3273623197, 3188840911, 3106765792, 3027290529, 2950312983, 2875735889, 2803466577, 2733416709, 2665502043, 2599642202, 2535760468, 2473783577, 2413641544, 2355267482, 2298597445, 2243570270, 2190127442, 2138212952, 2087773175, 2038756751, 1991114469, 1944799168, 1899765630, 1855970492, 1813372155, 1771930699, 1731607807, 1692366685, 1654171998, 1616989796, 1580787456, 1545533617, 1511198127, 1477751987, 1445167299, 1413417218, 1382475907, 1352318489, 1322921012, 1294260401, 1266314428, 1239061669, 1212481475, 1186553939, 1161259862, 1136580724, 1112498660, 1088996427, 1066057384, 1043665465, 1021805154, 1000461467, 979619926, 959266544, 939387802, 919970630, 901002394, 882470872, 864364246, 846671081, 829380310, 812481224, 795963455, 779816966, 764032035, 748599247, 733509480, 718753894, 704323923, 690211263, 676407865, 662905922, 649697861, 636776340, 624134232, 611764624, 599660803, 587816256, 576224658, 564879867, 553775919, 542907020, 532267539, 521852009, 511655112, 501671682, 491896696, 482325269, 472952653, 463774228, 454785499, 445982097, 437359765, 428914365, 420641868, 412538349, 404599991, 396823075]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 962).prefactor = (4868596027148149/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 962).cutoff/(generalMeanRows 962).c)).2 =
    (75078680227193/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 962).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 962).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 962).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 962

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 962).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 962).criticalRate j.val*(generalMeanRows 962).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 962).c*(generalMeanRows 962).criticalPoint j.val)).2-
      (generalMeanRows 962).J/2-(generalMeanRows 962).error (generalMeanGrid j.val)+
      (generalMeanRows 962).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 962).c)).2-
      (generalMeanRows 962).J/2-(generalMeanRows 962).error 4 := by
  have he : (generalMeanRows 962).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 962) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 962)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0962

/-! Kernel-checked entropy margins for general spectral rectangle 963. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0963
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5944986245, 5753316526, 5569489244, 5393090992, 5223736624, 5061066757, 4904745550, 4754458725, 4609911796, 4470828482, 4336949278, 4208030169, 4083841465, 3964166746, 3848801905, 3737554272, 3630241825, 3526692455, 3426743307, 3330240165, 3237036893, 3146994915, 3059982744, 2975875538, 2894554696, 2815907479, 2739826664, 2666210219, 2594961000, 2525986475, 2459198459, 2394512875, 2331849524, 2271131872, 2212286855, 2155244691, 2099938707, 2046305176, 1994283164, 1943814383, 1894843062, 1847315816, 1801181527, 1756391232, 1712898016, 1670656913, 1629624812, 1589760365, 1551023908, 1513377376, 1476784230, 1441209389, 1406619156, 1372981160, 1340264294, 1308438656, 1277475496, 1247347165, 1218027065, 1189489604, 1161710150, 1134664991, 1108331293, 1082687065, 1057711121, 1033383046, 1009683164, 986592506, 964092781, 942166350, 920796193, 899965892, 879659599, 859862016, 840558374, 821734410, 803376347, 785470874, 768005131, 750966687, 734343524, 718124025, 702296953, 686851441, 671776974, 657063378, 642700808, 628679732, 614990922, 601625443, 588574642, 575830135, 563383799, 551227766, 539354405, 527756324, 516426353, 505357541, 494543145, 483976625, 473651637, 463562024, 453701811, 444065200, 434646559, 425440423, 416441484, 407644585, 399044720, 390637023, 382416767, 374379357, 366520329, 358835342, 351320177, 343970730, 336783011, 329753140, 322877342, 316151944, 309573373]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 963).prefactor = (4859984962732511/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 963).cutoff/(generalMeanRows 963).c)).2 =
    (9051794576087/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 963).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 963).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 963).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 963

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 963).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 963).criticalRate j.val*(generalMeanRows 963).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 963).c*(generalMeanRows 963).criticalPoint j.val)).2-
      (generalMeanRows 963).J/2-(generalMeanRows 963).error (generalMeanGrid j.val)+
      (generalMeanRows 963).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 963).c)).2-
      (generalMeanRows 963).J/2-(generalMeanRows 963).error 4 := by
  have he : (generalMeanRows 963).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 963) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 963)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0963

/-! Kernel-checked entropy margins for general spectral rectangle 964. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0964
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5703000902, 5515353478, 5335481627, 5162972773, 4997442571, 4838532419, 4685907248, 4539253548, 4398277602, 4262703902, 4132273722, 4006743835, 3885885346, 3769482640, 3657332423, 3549242848, 3445032719, 3344530766, 3247574974, 3154011973, 3063696477, 2976490762, 2892264195, 2810892788, 2732258790, 2656250316, 2582760988, 2511689619, 2442939905, 2376420145, 2312042984, 2249725162, 2189387292, 2130953644, 2074351947, 2019513205, 1966371519, 1914863925, 1864930242, 1816512926, 1769556935, 1724009603, 1679820518, 1636941414, 1595326057, 1554930153, 1515711247, 1477628639, 1440643296, 1404717776, 1369816149, 1335903927, 1302948000, 1270916569, 1239779085, 1209506194, 1180069683, 1151442426, 1123598340, 1096512333, 1070160262, 1044518896, 1019565869, 995279647, 971639491, 948625423, 926218193, 904399250, 883150709, 862455328, 842296476, 822658113, 803524762, 784881486, 766713870, 749007993, 731750415, 714928154, 698528671, 682539846, 666949969, 651747721, 636922155, 622462690, 608359088, 594601448, 581180188, 568086037, 555310019, 542843447, 530677908, 518805255, 507217596, 495907287, 484866921, 474089317, 463567518, 453294778, 443264557, 433470511, 423906488, 414566521, 405444819, 396535764, 387833901, 379333939, 371030738, 362919309, 354994806, 347252523, 339687889, 332296463, 325073929, 318016094, 311118882, 304378330, 297790588, 291351909, 285058653, 278907277, 272894336]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 964).prefactor = (2420675945520867/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 964).cutoff/(generalMeanRows 964).c)).2 =
    (7279972187519/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 964).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 964).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 964).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 964

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 964).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 964).criticalRate j.val*(generalMeanRows 964).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 964).c*(generalMeanRows 964).criticalPoint j.val)).2-
      (generalMeanRows 964).J/2-(generalMeanRows 964).error (generalMeanGrid j.val)+
      (generalMeanRows 964).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 964).c)).2-
      (generalMeanRows 964).J/2-(generalMeanRows 964).error 4 := by
  have he : (generalMeanRows 964).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 964) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 964)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0964

/-! Kernel-checked entropy margins for general spectral rectangle 965. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0965
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5754169406, 5578005634, 5409076011, 5246989319, 5091381456, 4941913049, 4798267325, 4660148222, 4527278689, 4399399160, 4276266181, 4157651173, 4043339305, 3933128480, 3826828408, 3724259761, 3625253407, 3529649703, 3437297851, 3348055306, 3261787232, 3178366001, 3097670730, 3019586855, 2944005739, 2870824303, 2799944691, 2731273951, 2664723751, 2600210099, 2537653099, 2476976708, 2418108521, 2360979563, 2305524102, 2251679464, 2199385871, 2148586279, 2099226234, 2051253733, 2004619095, 1959274836, 1915175560, 1872277847, 1830540156, 1789922722, 1750387477, 1711897955, 1674419219, 1637917785, 1602361545, 1567719709, 1533962733, 1501062267, 1468991091, 1437723067, 1407233083, 1377497011, 1348491658, 1320194722, 1292584752, 1265641113, 1239343944, 1213674124, 1188613242, 1164143563, 1140248001, 1116910085, 1094113938, 1071844249, 1050086249, 1028825688, 1008048811, 987742340, 967893453, 948489765, 929519310, 910970522, 892832222, 875093600, 857744200, 840773909, 824172936, 807931810, 792041357, 776492695, 761277221, 746386598, 731812748, 717547842, 703584286, 689914719, 676531999, 663429199, 650599593, 638036657, 625734053, 613685631, 601885413, 590327596, 579006539, 567916761, 557052932, 546409873, 535982545, 525766051, 515755622, 505946622, 496334538, 486914977, 477683662, 468636432, 459769230, 451078108, 442559218, 434208813, 426023238, 417998936, 410132434, 402420350, 394859384]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 965).prefactor = (4617589831488557/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 965).cutoff/(generalMeanRows 965).c)).2 =
    (177832407995967/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 965).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 965).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 965).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 965

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 965).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 965).criticalRate j.val*(generalMeanRows 965).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 965).c*(generalMeanRows 965).criticalPoint j.val)).2-
      (generalMeanRows 965).J/2-(generalMeanRows 965).error (generalMeanGrid j.val)+
      (generalMeanRows 965).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 965).c)).2-
      (generalMeanRows 965).J/2-(generalMeanRows 965).error 4 := by
  have he : (generalMeanRows 965).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 965) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 965)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0965

/-! Kernel-checked entropy margins for general spectral rectangle 966. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0966
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5601803338, 5429623636, 5264562982, 5106233304, 4954273533, 4808347235, 4668140496, 4533360032, 4403731503, 4278997990, 4158918626, 4043267360, 3931831838, 3824412384, 3720821081, 3620880923, 3524425052, 3431296050, 3341345298, 3254432381, 3170424548, 3089196210, 3010628477, 2934608732, 2861030240, 2789791780, 2720797306, 2653955638, 2589180165, 2526388580, 2465502622, 2406447845, 2349153397, 2293551817, 2239578842, 2187173231, 2136276595, 2086833244, 2038790036, 1992096245, 1946703427, 1902565302, 1859637639, 1817878151, 1777246391, 1737703661, 1699212920, 1661738704, 1625247043, 1589705386, 1555082535, 1521348576, 1488474817, 1456433725, 1425198877, 1394744903, 1365047435, 1336083061, 1307829282, 1280264467, 1253367814, 1227119311, 1201499702, 1176490449, 1152073705, 1128232277, 1104949604, 1082209721, 1059997239, 1038297319, 1017095645, 996378405, 976132267, 956344361, 937002257, 918093949, 899607834, 881532700, 863857706, 846572369, 829666548, 813130432, 796954524, 781129633, 765646857, 750497575, 735673435, 721166344, 706968457, 693072168, 679470103, 666155107, 653120240, 640358768, 627864152, 615630048, 603650291, 591918896, 580430048, 569178098, 558157552, 547363074, 536789473, 526431703, 516284853, 506344149, 496604944, 487062714, 477713059, 468551691, 459574439, 450777239, 442156130, 433707258, 425426863, 417311284, 409356951, 401560384, 393918191, 386427064, 379083774]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 966).prefactor = (916657400517623/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 966).cutoff/(generalMeanRows 966).c)).2 =
    (91641026612493/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 966).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 966).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 966).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 966

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 966).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 966).criticalRate j.val*(generalMeanRows 966).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 966).c*(generalMeanRows 966).criticalPoint j.val)).2-
      (generalMeanRows 966).J/2-(generalMeanRows 966).error (generalMeanGrid j.val)+
      (generalMeanRows 966).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 966).c)).2-
      (generalMeanRows 966).J/2-(generalMeanRows 966).error 4 := by
  have he : (generalMeanRows 966).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 966) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 966)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0966

/-! Kernel-checked entropy margins for general spectral rectangle 967. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0967
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5123849968, 4949387035, 4782372085, 4622400895, 4469097132, 4322109908, 4181111609, 4045795954, 3915876248, 3791083826, 3671166638, 3555887976, 3445025324, 3338369308, 3235722749, 3136899788, 3041725104, 2950033177, 2861667637, 2776480642, 2694332325, 2615090276, 2538629063, 2464829797, 2393579720, 2324771832, 2258304539, 2194081333, 2132010485, 2072004773, 2013981210, 1957860813, 1903568368, 1851032220, 1800184078, 1750958825, 1703294351, 1657131385, 1612413344, 1569086195, 1527098314, 1486400366, 1446945182, 1408687652, 1371584617, 1335594773, 1300678575, 1266798154, 1233917228, 1202001030, 1171016233, 1140930877, 1111714309, 1083337115, 1055771067, 1028989063, 1002965077, 977674106, 953092129, 929196055, 905963687, 883373676, 861405488, 840039365, 819256291, 799037959, 779366743, 760225662, 741598361, 723469076, 705822614, 688644328, 671920090, 655636275, 639779738, 624337792, 609298193, 594649118, 580379150, 566477263, 552932805, 539735481, 526875343, 514342772, 502128469, 490223441, 478618988, 467306695, 456278416, 445526269, 435042624, 424820092, 414851518, 405129973, 395648744, 386401324, 377381411, 368582895, 359999852, 351626539, 343457387, 335486994, 327710121, 320121683, 312716746, 305490524, 298438369, 291555770, 284838345, 278281842, 271882128, 265635192, 259537133, 253584166, 247772608, 242098883, 236559514, 231151120, 225870416, 220714206, 215679383]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 967).prefactor = (2367334416394717/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 967).cutoff/(generalMeanRows 967).c)).2 =
    (156609062872339/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 967).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 967).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 967).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 967

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 967).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 967).criticalRate j.val*(generalMeanRows 967).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 967).c*(generalMeanRows 967).criticalPoint j.val)).2-
      (generalMeanRows 967).J/2-(generalMeanRows 967).error (generalMeanGrid j.val)+
      (generalMeanRows 967).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 967).c)).2-
      (generalMeanRows 967).J/2-(generalMeanRows 967).error 4 := by
  have he : (generalMeanRows 967).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 967) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 967)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0967

/-! Kernel-checked entropy margins for general spectral rectangle 968. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0968
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5129570649, 4958669669, 4795050231, 4638313701, 4488089132, 4344030843, 4205816260, 4073143981, 3945732050, 3823316399, 3705649446, 3592498828, 3483646250, 3378886449, 3278026239, 3180883653, 3087287150, 2997074893, 2910094091, 2826200385, 2745257296, 2667135707, 2591713387, 2518874557, 2448509483, 2380514101, 2314789669, 2251242446, 2189783390, 2130327884, 2072795470, 2017109615, 1963197481, 1910989715, 1860420255, 1811426145, 1763947363, 1717926662, 1673309418, 1630043487, 1588079077, 1547368622, 1507866662, 1469529737, 1432316283, 1396186534, 1361102431, 1327027535, 1293926949, 1261767237, 1230516355, 1200143581, 1170619452, 1141915703, 1114005210, 1086861932, 1060460867, 1034777996, 1009790242, 985475422, 961812211, 938780100, 916359358, 894531000, 873276749, 852579010, 832420836, 812785902, 793658474, 775023390, 756866027, 739172286, 721928566, 705121741, 688739143, 672768545, 657198138, 642016514, 627212656, 612775913, 598695995, 584962950, 571567154, 558499301, 545750386, 533311695, 521174794, 509331519, 497773963, 486494470, 475485621, 464740231, 454251334, 444012180, 434016225, 424257121, 414728715, 405425035, 396340290, 387468858, 378805285, 370344275, 362080686, 354009527, 346125948, 338425240, 330902826, 323554262, 316375226, 309361519, 302509059, 295813875, 289272110, 282880009, 276633921, 270530296, 264565678, 258736704, 253040104, 247472692, 242031370]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 968).prefactor = (4685024656925089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 968).cutoff/(generalMeanRows 968).c)).2 =
    (33101969599/97656250000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 968).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 968).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 968).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 968

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 968).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 968).criticalRate j.val*(generalMeanRows 968).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 968).c*(generalMeanRows 968).criticalPoint j.val)).2-
      (generalMeanRows 968).J/2-(generalMeanRows 968).error (generalMeanGrid j.val)+
      (generalMeanRows 968).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 968).c)).2-
      (generalMeanRows 968).J/2-(generalMeanRows 968).error 4 := by
  have he : (generalMeanRows 968).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 968) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 968)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0968

/-! Kernel-checked entropy margins for general spectral rectangle 969. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0969
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5298212217, 5130387949, 4969638176, 4815571358, 4667823422, 4526055361, 4389951078, 4259215474, 4133572721, 4012764716, 3896549681, 3784700906, 3677005603, 3573263867, 3473287734, 3376900319, 3283935027, 3194234838, 3107651647, 3024045655, 2943284817, 2865244326, 2789806145, 2716858568, 2646295818, 2578017673, 2511929122, 2447940045, 2385964914, 2325922518, 2267735704, 2211331139, 2156639088, 2103593201, 2052130328, 2002190326, 1953715898, 1906652433, 1860947853, 1816552479, 1773418897, 1731501840, 1690758066, 1651146260, 1612626923, 1575162282, 1538716203, 1503254099, 1468742859, 1435150766, 1402447432, 1370603731, 1339591732, 1309384646, 1279956767, 1251283417, 1223340904, 1196106466, 1169558232, 1143675179, 1118437093, 1093824529, 1069818776, 1046401827, 1023556342, 1001265619, 979513569, 958284685, 937564015, 917337142, 897590159, 878309644, 859482643, 841096648, 823139579, 805599765, 788465928, 771727165, 755372935, 739393043, 723777624, 708517134, 693602334, 679024278, 664774302, 650844014, 637225282, 623910226, 610891204, 598160808, 585711854, 573537370, 561630593, 549984959, 538594095, 527451814, 516552106, 505889136, 495457231, 485250881, 475264730, 465493570, 455932338, 446576110, 437420097, 428459639, 419690203, 411107376, 402706863, 394484483, 386436165, 378557945, 370845960, 363296450, 355905750, 348670288, 341586584, 334651246, 327860968, 321212525, 314702773]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 969).prefactor = (925925957871659/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 969).cutoff/(generalMeanRows 969).c)).2 =
    (189286653394403/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 969).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 969).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 969).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 969

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 969).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 969).criticalRate j.val*(generalMeanRows 969).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 969).c*(generalMeanRows 969).criticalPoint j.val)).2-
      (generalMeanRows 969).J/2-(generalMeanRows 969).error (generalMeanGrid j.val)+
      (generalMeanRows 969).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 969).c)).2-
      (generalMeanRows 969).J/2-(generalMeanRows 969).error 4 := by
  have he : (generalMeanRows 969).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 969) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 969)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0969

/-! Kernel-checked entropy margins for general spectral rectangle 970. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0970
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5373594234, 5201124074, 5035953315, 4877678273, 4725923554, 4580339572, 4440600343, 4306401507, 4177458552, 4053505226, 3934292095, 3819585245, 3709165105, 3602825381, 3500372079, 3401622621, 3306405037, 3214557222, 3125926258, 3040367793, 2957745462, 2877930368, 2800800590, 2726240734, 2654141523, 2584399408, 2516916213, 2451598807, 2388358798, 2327112246, 2267779397, 2210284444, 2154555286, 2100523322, 2048123249, 1997292873, 1947972936, 1900106952, 1853641055, 1808523853, 1764706297, 1722141553, 1680784881, 1640593532, 1601526634, 1563545100, 1526611534, 1490690144, 1455746660, 1421748258, 1388663486, 1356462196, 1325115481, 1294595611, 1264875979, 1235931043, 1207736279, 1180268128, 1153503953, 1127421996, 1102001334, 1077221843, 1053064162, 1029509653, 1006540373, 984139043, 962289014, 940974242, 920179260, 899889157, 880089544, 860766544, 841906760, 823497258, 805525550, 787979571, 770847663, 754118560, 737781370, 721825559, 706240938, 691017649, 676146151, 661617209, 647421880, 633551502, 619997686, 606752299, 593807464, 581155539, 568789118, 556701015, 544884262, 533332095, 522037952, 510995460, 500198435, 489640870, 479316928, 469220942, 459347405, 449690962, 440246410, 431008692, 421972886, 413134210, 404488009, 396029756, 387755044, 379659587, 371739211, 363989853, 356407557, 348988470, 341728842, 334625017, 327673435, 320870626, 314213211, 307697894, 301321464]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 970).prefactor = (4768346578662923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 970).cutoff/(generalMeanRows 970).c)).2 =
    (372058625767613/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 970).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 970).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 970).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 970

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 970).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 970).criticalRate j.val*(generalMeanRows 970).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 970).c*(generalMeanRows 970).criticalPoint j.val)).2-
      (generalMeanRows 970).J/2-(generalMeanRows 970).error (generalMeanGrid j.val)+
      (generalMeanRows 970).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 970).c)).2-
      (generalMeanRows 970).J/2-(generalMeanRows 970).error 4 := by
  have he : (generalMeanRows 970).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 970) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 970)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0970

/-! Kernel-checked entropy margins for general spectral rectangle 971. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0971
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5367733527, 5190969996, 5021749720, 4859656012, 4704301321, 4555324678, 4412389425, 4275181176, 4143406001, 4016788779, 3895071722, 3778013038, 3665385720, 3556976445, 3452584574, 3352021240, 3255108514, 3161678646, 3071573362, 2984643223, 2900747039, 2819751323, 2741529789, 2665962896, 2592937411, 2522346025, 2454086976, 2388063717, 2324184596, 2262362563, 2202514900, 2144562965, 2088431954, 2034050681, 1981351374, 1930269479, 1880743481, 1832714735, 1786127310, 1740927839, 1697065382, 1654491293, 1613159101, 1573024397, 1534044718, 1496179455, 1459389754, 1423638424, 1388889855, 1355109939, 1322265993, 1290326690, 1259261991, 1229043082, 1199642315, 1171033153, 1143190114, 1116088723, 1089705464, 1064017735, 1039003806, 1014642776, 990914539, 967799748, 945279774, 923336682, 901953196, 881112668, 860799056, 840996892, 821691260, 802867771, 784512543, 766612176, 749153733, 732124721, 715513074, 699307131, 683495626, 668067665, 653012715, 638320589, 623981432, 609985707, 596324185, 582987929, 569968287, 557256878, 544845583, 532726535, 520892109, 509334914, 498047782, 487023764, 476256118, 465738302, 455463970, 445426960, 435621294, 426041164, 416680932, 407535121, 398598411, 389865632, 381331761, 372991916, 364841350, 356875447, 349089722, 341479810, 334041465, 326770558, 319663071, 312715093, 305922819, 299282544, 292790662, 286443663, 280238126, 274170722, 268238208]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 971).prefactor = (491121971491331/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 971).cutoff/(generalMeanRows 971).c)).2 =
    (44894402616463/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 971).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 971).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 971).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 971

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 971).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 971).criticalRate j.val*(generalMeanRows 971).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 971).c*(generalMeanRows 971).criticalPoint j.val)).2-
      (generalMeanRows 971).J/2-(generalMeanRows 971).error (generalMeanGrid j.val)+
      (generalMeanRows 971).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 971).c)).2-
      (generalMeanRows 971).J/2-(generalMeanRows 971).error 4 := by
  have he : (generalMeanRows 971).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 971) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 971)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0971

/-! Kernel-checked entropy margins for general spectral rectangle 972. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0972
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5445067133, 5263499409, 5089713099, 4923278538, 4763796066, 4610893410, 4464223333, 4323461549, 4188304841, 4058469371, 3933689164, 3813714723, 3698311788, 3587260201, 3480352877, 3377394863, 3278202482, 3182602549, 3090431647, 3001535471, 2915768219, 2832992032, 2753076480, 2675898084, 2601339879, 2529291003, 2459646324, 2392306083, 2327175578, 2264164854, 2203188427, 2144165018, 2087017312, 2031671731, 1978058216, 1926110037, 1875763599, 1826958273, 1779636232, 1733742299, 1689223802, 1646030443, 1604114171, 1563429061, 1523931208, 1485578617, 1448331109, 1412150226, 1376999145, 1342842595, 1309646779, 1277379304, 1246009108, 1215506399, 1185842589, 1156990240, 1128923009, 1101615591, 1075043678, 1049183906, 1024013813, 999511799, 975657085, 952429677, 929810329, 907780509, 886322369, 865418717, 845052981, 825209189, 805871940, 787026379, 768658175, 750753500, 733299003, 716281796, 699689431, 683509881, 667731529, 652343144, 637333868, 622693203, 608410994, 594477419, 580882971, 567618449, 554674945, 542043835, 529716766, 517685643, 505942626, 494480117, 483290747, 472367377, 461703079, 451291136, 441125032, 431198445, 421505237, 412039453, 402795311, 393767197, 384949658, 376337399, 367925275, 359708287, 351681578, 343840426, 336180242, 328696564, 321385054, 314241492, 307261774, 300441909, 293778012, 287266305, 280903109, 274684846, 268608030, 262669271, 256865266]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 972).prefactor = (632296716750941/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 972).cutoff/(generalMeanRows 972).c)).2 =
    (352765422832933/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 972).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 972).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 972).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 972

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 972).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 972).criticalRate j.val*(generalMeanRows 972).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 972).c*(generalMeanRows 972).criticalPoint j.val)).2-
      (generalMeanRows 972).J/2-(generalMeanRows 972).error (generalMeanGrid j.val)+
      (generalMeanRows 972).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 972).c)).2-
      (generalMeanRows 972).J/2-(generalMeanRows 972).error 4 := by
  have he : (generalMeanRows 972).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 972) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 972)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0972

/-! Kernel-checked entropy margins for general spectral rectangle 973. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0973
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5694217448, 5506702554, 5327189721, 5155236919, 4990433025, 4832395113, 4680766048, 4535212324, 4395422132, 4261103617, 4131983312, 4007804719, 3888327022, 3773323924, 3662582582, 3555902642, 3453095353, 3353982760, 3258396964, 3166179437, 3077180400, 2991258247, 2908279012, 2828115881, 2750648737, 2675763741, 2603352944, 2533313924, 2465549456, 2399967195, 2336479393, 2275002623, 2215457531, 2157768604, 2101863945, 2047675074, 1995136735, 1944186716, 1894765685, 1846817027, 1800286705, 1755123114, 1711276958, 1668701123, 1627350567, 1587182210, 1548154833, 1510228984, 1473366888, 1437532362, 1402690735, 1368808774, 1335854614, 1303797688, 1272608666, 1242259397, 1212722849, 1183973059, 1155985080, 1128734935, 1102199572, 1076356821, 1051185352, 1026664640, 1002774924, 979497179, 956813075, 934704956, 913155800, 892149201, 871669334, 851700937, 832229281, 813240152, 794719826, 776655052, 759033027, 741841384, 725068169, 708701826, 692731182, 677145431, 661934117, 647087125, 632594662, 618447250, 604635709, 591151148, 577984956, 565128786, 552574550, 540314406, 528340753, 516646216, 505223645, 494066099, 483166847, 472519352, 462117272, 451954445, 442024892, 432322802, 422842530, 413578594, 404525664, 395678561, 387032249, 378581833, 370322554, 362249780, 354359010, 346645862, 339106073, 331735495, 324530091, 317485933, 310599192, 303866146, 297283168, 290846724, 284553374]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 973).prefactor = (5209936903291017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 973).cutoff/(generalMeanRows 973).c)).2 =
    (44894402616463/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 973).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 973).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 973).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 973

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 973).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 973).criticalRate j.val*(generalMeanRows 973).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 973).c*(generalMeanRows 973).criticalPoint j.val)).2-
      (generalMeanRows 973).J/2-(generalMeanRows 973).error (generalMeanGrid j.val)+
      (generalMeanRows 973).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 973).c)).2-
      (generalMeanRows 973).J/2-(generalMeanRows 973).error 4 := by
  have he : (generalMeanRows 973).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 973) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 973)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0973

/-! Kernel-checked entropy margins for general spectral rectangle 974. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0974
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6050988458, 5859319520, 5675730230, 5499773416, 5331033280, 5169122645, 5013680505, 4864369833, 4720875609, 4582903059, 4450176055, 4322435675, 4199438896, 4080957412, 3966776552, 3856694299, 3750520389, 3648075492, 3549190459, 3453705629, 3361470195, 3272341619, 3186185093, 3102873038, 3022284649, 2944305464, 2868826974, 2795746254, 2724965624, 2656392333, 2589938268, 2525519676, 2463056913, 2402474205, 2343699425, 2286663889, 2231302157, 2177551859, 2125353519, 2074650397, 2025388346, 1977515663, 1930982967, 1885743068, 1841750858, 1798963197, 1757338816, 1716838215, 1677423576, 1639058679, 1601708818, 1565340725, 1529922505, 1495423561, 1461814534, 1429067241, 1397154622, 1366050683, 1335730445, 1306169898, 1277345955, 1249236408, 1221819890, 1195075833, 1168984434, 1143526619, 1118684013, 1094438903, 1070774216, 1047673486, 1025120828, 1003100914, 981598951, 960600652, 940092221, 920060330, 900492097, 881375071, 862697213, 844446878, 826612803, 809184085, 792150172, 775500848, 759226219, 743316699, 727763002, 712556126, 697687346, 683148201, 668930485, 655026236, 641427730, 628127470, 615118179, 602392789, 589944439, 577766461, 565852379, 554195899, 542790903, 531631445, 520711742, 510026170, 499569260, 489335690, 479320282, 469517996, 459923929, 450533303, 441341471, 432343904, 423536191, 414914038, 406473258, 398209773, 390119609, 382198890, 374443841, 366850779, 359416114]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 974).prefactor = (5287413050563001/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 974).cutoff/(generalMeanRows 974).c)).2 =
    (189286653394403/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 974).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 974).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 974).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 974

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 974).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 974).criticalRate j.val*(generalMeanRows 974).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 974).c*(generalMeanRows 974).criticalPoint j.val)).2-
      (generalMeanRows 974).J/2-(generalMeanRows 974).error (generalMeanGrid j.val)+
      (generalMeanRows 974).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 974).c)).2-
      (generalMeanRows 974).J/2-(generalMeanRows 974).error 4 := by
  have he : (generalMeanRows 974).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 974) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 974)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0974

/-! Kernel-checked entropy margins for general spectral rectangle 975. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0975
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7523302539, 7314444272, 7113565305, 6920254478, 6734128845, 6554831125, 6382027455, 6215405382, 6054672082, 5899552756, 5749789200, 5605138515, 5465371942, 5330273810, 5199640583, 5073279994, 4951010257, 4832659343, 4718064327, 4607070783, 4499532232, 4395309633, 4294270914, 4196290545, 4101249134, 4009033062, 3919534140, 3832649292, 3748280263, 3666333344, 3586719116, 3509352218, 3434151117, 3361037911, 3289938128, 3220780549, 3153497037, 3088022378, 3024294135, 2962252502, 2901840177, 2843002236, 2785686017, 2729841010, 2675418755, 2622372740, 2570658312, 2520232590, 2471054382, 2423084105, 2376283714, 2330616631, 2286047678, 2242543018, 2200070088, 2158597552, 2118095239, 2078534098, 2039886147, 2002124426, 1965222957, 1929156699, 1893901509, 1859434107, 1825732036, 1792773631, 1760537987, 1729004923, 1698154959, 1667969283, 1638429727, 1609518737, 1581219356, 1553515191, 1526390400, 1499829664, 1473818167, 1448341583, 1423386048, 1398938149, 1374984903, 1351513743, 1328512502, 1305969397, 1283873013, 1262212295, 1240976528, 1220155329, 1199738633, 1179716681, 1160080012, 1140819446, 1121926081, 1103391279, 1085206656, 1067364077, 1049855642, 1032673682, 1015810749, 999259608, 983013232, 967064790, 951407647, 936035351, 920941631, 906120390, 891565696, 877271782, 863233035, 849443996, 835899351, 822593927, 809522689, 796680736, 784063292, 771665709, 759483456, 747512120, 735747400, 724185107, 712821153]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 975).prefactor = (4943903832718927/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 975).cutoff/(generalMeanRows 975).c)).2 =
    (78037294638943/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 975).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 975).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 975).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 975

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 975).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 975).criticalRate j.val*(generalMeanRows 975).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 975).c*(generalMeanRows 975).criticalPoint j.val)).2-
      (generalMeanRows 975).J/2-(generalMeanRows 975).error (generalMeanGrid j.val)+
      (generalMeanRows 975).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 975).c)).2-
      (generalMeanRows 975).J/2-(generalMeanRows 975).error 4 := by
  have he : (generalMeanRows 975).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 975) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 975)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0975

/-! Kernel-checked entropy margins for general spectral rectangle 976. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0976
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7086312500, 6879715828, 6681137312, 6490163002, 6306407278, 6129510309, 5959135799, 5794968985, 5636714844, 5484096494, 5336853758, 5194741867, 5057530292, 4925001692, 4796950953, 4673184314, 4553518583, 4437780403, 4325805596, 4217438556, 4112531691, 4010944911, 3912545157, 3817205967, 3724807073, 3635234030, 3548377870, 3464134787, 3382405836, 3303096659, 3226117225, 3151381596, 3078807701, 3008317124, 2939834913, 2873289398, 2808612014, 2745737146, 2684601977, 2625146346, 2567312614, 2511045540, 2456292165, 2403001695, 2351125405, 2300616532, 2251430188, 2203523269, 2156854369, 2111383709, 2067073056, 2023885654, 1981786158, 1940740571, 1900716182, 1861681512, 1823606258, 1786461241, 1750218359, 1714850540, 1680331699, 1646636692, 1613741282, 1581622097, 1550256595, 1519623030, 1489700419, 1460468511, 1431907756, 1403999277, 1376724844, 1350066849, 1324008276, 1298532685, 1273624183, 1249267406, 1225447498, 1202150090, 1179361283, 1157067628, 1135256110, 1113914133, 1093029500, 1072590402, 1052585404, 1033003426, 1013833736, 995065931, 976689931, 958695964, 941074555, 923816516, 906912934, 890355165, 874134820, 858243758, 842674080, 827418113, 812468412, 797817744, 783459084, 769385608, 755590687, 742067877, 728810916, 715813717, 703070361, 690575094, 678322318, 666306589, 654522610, 642965227, 631629425, 620510322, 609603166, 598903330, 588406307, 578107712, 568003269, 558088814, 548360291]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 976).prefactor = (1240786087766947/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 976).cutoff/(generalMeanRows 976).c)).2 =
    (7433282847129/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 976).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 976).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 976).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 976

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 976).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 976).criticalRate j.val*(generalMeanRows 976).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 976).c*(generalMeanRows 976).criticalPoint j.val)).2-
      (generalMeanRows 976).J/2-(generalMeanRows 976).error (generalMeanGrid j.val)+
      (generalMeanRows 976).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 976).c)).2-
      (generalMeanRows 976).J/2-(generalMeanRows 976).error 4 := by
  have he : (generalMeanRows 976).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 976) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 976)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0976

/-! Kernel-checked entropy margins for general spectral rectangle 977. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0977
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6714757997, 6511285374, 6315834667, 6127990175, 5947364595, 5773596491, 5606348041, 5445303033, 5290165079, 5140656010, 4996514441, 4857494469, 4723364513, 4593906244, 4468913633, 4348192072, 4231557579, 4118836074, 4009862712, 3904481271, 3802543596, 3703909084, 3608444208, 3516022081, 3426522050, 3339829323, 3255834624, 3174433868, 3095527865, 3019022039, 2944826172, 2872854163, 2803023799, 2735256549, 2669477363, 2605614493, 2543599315, 2483366170, 2424852213, 2367997268, 2312743696, 2259036266, 2206822041, 2156050261, 2106672240, 2058641266, 2011912509, 1966442928, 1922191191, 1879117595, 1837183990, 1796353706, 1756591492, 1717863446, 1680136957, 1643380647, 1607564319, 1572658903, 1538636405, 1505469865, 1473133312, 1441601717, 1410850958, 1380857782, 1351599762, 1323055273, 1295203450, 1268024160, 1241497973, 1215606133, 1190330528, 1165653669, 1141558662, 1118029183, 1095049459, 1072604245, 1050678803, 1029258879, 1008330694, 987880913, 967896639, 948365389, 929275082, 910614024, 892370891, 874534717, 857094880, 840041092, 823363380, 807052085, 791097838, 775491562, 760224451, 745287968, 730673832, 716374006, 702380697, 688686337, 675283585, 662165310, 649324591, 636754707, 624449129, 612401514, 600605702, 589055704, 577745702, 566670040, 555823219, 545199891, 534794858, 524603063, 514619586, 504839641, 495258573, 485871848, 476675056, 467663903, 458834209, 450181903, 441703022]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 977).prefactor = (4968678662322879/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 977).cutoff/(generalMeanRows 977).c)).2 =
    (288249609356927/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 977).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 977).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 977).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 977

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 977).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 977).criticalRate j.val*(generalMeanRows 977).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 977).c*(generalMeanRows 977).criticalPoint j.val)).2-
      (generalMeanRows 977).J/2-(generalMeanRows 977).error (generalMeanGrid j.val)+
      (generalMeanRows 977).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 977).c)).2-
      (generalMeanRows 977).J/2-(generalMeanRows 977).error 4 := by
  have he : (generalMeanRows 977).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 977) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 977)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0977

/-! Kernel-checked entropy margins for general spectral rectangle 978. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0978
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6400872090, 6201076605, 6009273969, 5825047857, 5648010366, 5477799485, 5314076854, 5156525762, 5004849367, 4858769090, 4718023182, 4582365424, 4451563959, 4325400234, 4203668034, 4086172608, 3972729872, 3863165682, 3757315163, 3655022100, 3556138375, 3460523453, 3368043903, 3278572959, 3191990115, 3108180748, 3027035770, 2948451305, 2872328388, 2798572684, 2727094232, 2657807197, 2590629648, 2525483343, 2462293532, 2400988774, 2341500760, 2283764151, 2227716429, 2173297746, 2120450799, 2069120692, 2019254825, 1970802780, 1923716212, 1877948749, 1833455902, 1790194971, 1748124964, 1707206516, 1667401812, 1628674518, 1590989714, 1554313827, 1518614573, 1483860899, 1450022926, 1417071902, 1384980147, 1353721011, 1323268828, 1293598872, 1264687319, 1236511209, 1209048409, 1182277576, 1156178129, 1130730214, 1105914673, 1081713020, 1058107411, 1035080616, 1012615999, 990697489, 969309564, 948437223, 928065968, 908181787, 888771129, 869820894, 851318407, 833251409, 815608039, 798376816, 781546629, 765106719, 749046670, 733356393, 718026117, 703046374, 688407990, 674102074, 660120007, 646453434, 633094254, 620034608, 607266875, 594783661, 582577790, 570642302, 558970436, 547555634, 536391524, 525471922, 514790820, 504342382, 494120939, 484120982, 474337157, 464764262, 455397237, 446231166, 437261267, 428482889, 419891510, 411482728, 403252264, 395195953, 387309740, 379589681, 372031935]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 978).prefactor = (2480909655519023/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 978).cutoff/(generalMeanRows 978).c)).2 =
    (142237228199777/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 978).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 978).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 978).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 978

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 978).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 978).criticalRate j.val*(generalMeanRows 978).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 978).c*(generalMeanRows 978).criticalPoint j.val)).2-
      (generalMeanRows 978).J/2-(generalMeanRows 978).error (generalMeanGrid j.val)+
      (generalMeanRows 978).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 978).c)).2-
      (generalMeanRows 978).J/2-(generalMeanRows 978).error 4 := by
  have he : (generalMeanRows 978).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 978) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 978)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0978

/-! Kernel-checked entropy margins for general spectral rectangle 979. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0979
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6138894099, 5943111856, 5755263356, 5574932815, 5401732839, 5235301909, 5075302152, 4921417342, 4773351126, 4630825426, 4493579001, 4361366160, 4233955585, 4111129278, 3992681595, 3878418373, 3768156127, 3661721329, 3558949731, 3459685757, 3363781942, 3271098410, 3181502398, 3094867815, 3011074838, 2930009529, 2851563491, 2775633540, 2702121404, 2630933444, 2561980392, 2495177105, 2430442343, 2367698550, 2306871661, 2247890913, 2190688670, 2135200264, 2081363836, 2029120195, 1978412684, 1929187051, 1881391326, 1834975717, 1789892493, 1746095891, 1703542020, 1662188769, 1621995726, 1582924095, 1544936624, 1507997530, 1472072435, 1437128296, 1403133354, 1370057066, 1337870059, 1306544071, 1276051908, 1246367394, 1217465327, 1189321437, 1161912346, 1135215531, 1109209286, 1083872689, 1059185567, 1035128468, 1011682628, 988829944, 966552948, 944834780, 923659161, 903010374, 882873241, 863233097, 844075775, 825387583, 807155287, 789366094, 772007630, 755067932, 738535426, 722398912, 706647555, 691270866, 676258692, 661601202, 647288877, 633312495, 619663123, 606332107, 593311058, 580591847, 568166593, 556027655, 544167623, 532579308, 521255741, 510190155, 499375988, 488806870, 478476615, 468379223, 458508863, 448859875, 439426762, 430204182, 421186946, 412370014, 403748485, 395317597, 387072720, 379009353, 371123119, 363409763, 355865143, 348485234, 341266118, 334203982, 327295117]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 979).prefactor = (7910092530001/1600000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 979).cutoff/(generalMeanRows 979).c)).2 =
    (35708739225541/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 979).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 979).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 979).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 979

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 979).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 979).criticalRate j.val*(generalMeanRows 979).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 979).c*(generalMeanRows 979).criticalPoint j.val)).2-
      (generalMeanRows 979).J/2-(generalMeanRows 979).error (generalMeanGrid j.val)+
      (generalMeanRows 979).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 979).c)).2-
      (generalMeanRows 979).J/2-(generalMeanRows 979).error 4 := by
  have he : (generalMeanRows 979).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 979) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 979)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0979

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock13 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 13 i) := by
  fin_cases i
  · exact EntropyRow0910.numerical
  · exact EntropyRow0911.numerical
  · exact EntropyRow0912.numerical
  · exact EntropyRow0913.numerical
  · exact EntropyRow0914.numerical
  · exact EntropyRow0915.numerical
  · exact EntropyRow0916.numerical
  · exact EntropyRow0917.numerical
  · exact EntropyRow0918.numerical
  · exact EntropyRow0919.numerical
  · exact EntropyRow0920.numerical
  · exact EntropyRow0921.numerical
  · exact EntropyRow0922.numerical
  · exact EntropyRow0923.numerical
  · exact EntropyRow0924.numerical
  · exact EntropyRow0925.numerical
  · exact EntropyRow0926.numerical
  · exact EntropyRow0927.numerical
  · exact EntropyRow0928.numerical
  · exact EntropyRow0929.numerical
  · exact EntropyRow0930.numerical
  · exact EntropyRow0931.numerical
  · exact EntropyRow0932.numerical
  · exact EntropyRow0933.numerical
  · exact EntropyRow0934.numerical
  · exact EntropyRow0935.numerical
  · exact EntropyRow0936.numerical
  · exact EntropyRow0937.numerical
  · exact EntropyRow0938.numerical
  · exact EntropyRow0939.numerical
  · exact EntropyRow0940.numerical
  · exact EntropyRow0941.numerical
  · exact EntropyRow0942.numerical
  · exact EntropyRow0943.numerical
  · exact EntropyRow0944.numerical
  · exact EntropyRow0945.numerical
  · exact EntropyRow0946.numerical
  · exact EntropyRow0947.numerical
  · exact EntropyRow0948.numerical
  · exact EntropyRow0949.numerical
  · exact EntropyRow0950.numerical
  · exact EntropyRow0951.numerical
  · exact EntropyRow0952.numerical
  · exact EntropyRow0953.numerical
  · exact EntropyRow0954.numerical
  · exact EntropyRow0955.numerical
  · exact EntropyRow0956.numerical
  · exact EntropyRow0957.numerical
  · exact EntropyRow0958.numerical
  · exact EntropyRow0959.numerical
  · exact EntropyRow0960.numerical
  · exact EntropyRow0961.numerical
  · exact EntropyRow0962.numerical
  · exact EntropyRow0963.numerical
  · exact EntropyRow0964.numerical
  · exact EntropyRow0965.numerical
  · exact EntropyRow0966.numerical
  · exact EntropyRow0967.numerical
  · exact EntropyRow0968.numerical
  · exact EntropyRow0969.numerical
  · exact EntropyRow0970.numerical
  · exact EntropyRow0971.numerical
  · exact EntropyRow0972.numerical
  · exact EntropyRow0973.numerical
  · exact EntropyRow0974.numerical
  · exact EntropyRow0975.numerical
  · exact EntropyRow0976.numerical
  · exact EntropyRow0977.numerical
  · exact EntropyRow0978.numerical
  · exact EntropyRow0979.numerical
end SingularValueBounds.KL.Certificates
