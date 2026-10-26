import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 980. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0980
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6162938361, 5980022132, 5804468994, 5635885390, 5473904945, 5318186064, 5168409801, 5024277948, 4885511335, 4751848301, 4623043313, 4498865728, 4379098666, 4263537995, 4151991403, 4044277553, 3940225321, 3839673084, 3742468083, 3648465827, 3557529556, 3469529734, 3384343593, 3301854707, 3221952598, 3144532371, 3069494380, 2996743910, 2926190890, 2857749620, 2791338521, 2726879899, 2664299725, 2603527433, 2544495727, 2487140401, 2431400174, 2377216532, 2324533582, 2273297910, 2223458456, 2174966391, 2127775000, 2081839576, 2037117320, 1993567243, 1951150076, 1909828187, 1869565500, 1830327417, 1792080749, 1754793650, 1718435548, 1682977089, 1648390080, 1614647430, 1581723106, 1549592077, 1518230273, 1487614542, 1457722603, 1428533013, 1400025126, 1372179060, 1344975659, 1318396469, 1292423698, 1267040196, 1242229423, 1217975420, 1194262793, 1171076681, 1148402737, 1126227107, 1104536410, 1083317714, 1062558524, 1042246761, 1022370745, 1002919178, 983881132, 965246032, 947003643, 929144056, 911657674, 894535203, 877767639, 861346255, 845262594, 829508457, 814075891, 798957184, 784144854, 769631639, 755410494, 741474576, 727817242, 714432041, 701312706, 688453146, 675847445, 663489849, 651374766, 639496759, 627850538, 616430958, 605233012, 594251830, 583482670, 572920915, 562562071, 552401760, 542435719, 532659794, 523069939, 513662209, 504432760, 495377844, 486493808, 477777088, 469224209]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 980).prefactor = (1175004534835341/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 980).cutoff/(generalMeanRows 980).c)).2 =
    (350282048251219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 980).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 980).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 980).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 980

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 980).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 980).criticalRate j.val*(generalMeanRows 980).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 980).c*(generalMeanRows 980).criticalPoint j.val)).2-
      (generalMeanRows 980).J/2-(generalMeanRows 980).error (generalMeanGrid j.val)+
      (generalMeanRows 980).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 980).c)).2-
      (generalMeanRows 980).J/2-(generalMeanRows 980).error 4 := by
  have he : (generalMeanRows 980).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 980) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 980)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0980

/-! Kernel-checked entropy margins for general spectral rectangle 981. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0981
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5670765865, 5483974959, 5304931112, 5133222578, 4968465812, 4810302983, 4658399767, 4512443379, 4372140811, 4237217247, 4107414640, 3982490428, 3862216373, 3746377501, 3634771151, 3527206096, 3423501753, 3323487450, 3227001761, 3133891897, 3044013136, 2957228314, 2873407339, 2792426759, 2714169344, 2638523719, 2565384007, 2494649504, 2426224382, 2360017404, 2295941664, 2233914341, 2173856475, 2115692751, 2059351301, 2004763519, 1951863887, 1900589808, 1850881457, 1802681635, 1755935635, 1710591113, 1666597970, 1623908240, 1582475980, 1542257177, 1503209647, 1465292950, 1428468304, 1392698509, 1357947867, 1324182115, 1291368355, 1259474996, 1228471686, 1198329262, 1169019691, 1140516024, 1112792342, 1085823714, 1059586150, 1034056564, 1009212730, 985033248, 961497505, 938585644, 916278531, 894557725, 873405445, 852804548, 832738499, 813191347, 794147700, 775592703, 757512014, 739891789, 722718654, 705979693, 689662427, 673754795, 658245141, 643122196, 628375064, 613993207, 599966431, 586284874, 572938992, 559919549, 547217601, 534824493, 522731839, 510931518, 499415665, 488176657, 477207107, 466499856, 456047963, 445844699, 435883538, 426158151, 416662399, 407390325, 398336148, 389494260, 380859215, 372425727, 364188665, 356143043, 348284022, 340606900, 333107109, 325780209, 318621890, 311627957, 304794338, 298117070, 291592302, 285216290, 278985391, 272896063, 266944858]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 981).prefactor = (975774615203619/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 981).cutoff/(generalMeanRows 981).c)).2 =
    (29528537250377/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 981).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 981).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 981).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 981

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 981).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 981).criticalRate j.val*(generalMeanRows 981).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 981).c*(generalMeanRows 981).criticalPoint j.val)).2-
      (generalMeanRows 981).J/2-(generalMeanRows 981).error (generalMeanGrid j.val)+
      (generalMeanRows 981).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 981).c)).2-
      (generalMeanRows 981).J/2-(generalMeanRows 981).error 4 := by
  have he : (generalMeanRows 981).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 981) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 981)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0981

/-! Kernel-checked entropy margins for general spectral rectangle 982. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0982
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5505220499, 5322988390, 5148374206, 4980969873, 4820395353, 4666296184, 4518341286, 4376221005, 4239645363, 4108342485, 3982057179, 3860549664, 3743594403, 3630979062, 3522503551, 3417979156, 3317227744, 3220081038, 3126379952, 3035973980, 2948720637, 2864484937, 2783138923, 2704561223, 2628636643, 2555255794, 2484314737, 2415714663, 2349361592, 2285166089, 2223043008, 2162911243, 2104693506, 2048316112, 1993708782, 1940804459, 1889539130, 1839851667, 1791683675, 1744979344, 1699685320, 1655750576, 1613126292, 1571765747, 1531624208, 1492658837, 1454828593, 1418094145, 1382417790, 1347763372, 1314096210, 1281383027, 1249591882, 1218692112, 1188654266, 1159450054, 1131052291, 1103434848, 1076572602, 1050441395, 1025017986, 1000280011, 976205948, 952775077, 929967443, 907763828, 886145716, 865095264, 844595271, 824629155, 805180924, 786235151, 767776954, 749791969, 732266332, 715186658, 698540020, 682313934, 666496336, 651075570, 636040371, 621379846, 607083466, 593141045, 579542731, 566278992, 553340604, 540718639, 528404454, 516389680, 504666212, 493226200, 482062038, 471166357, 460532013, 450152084, 440019858, 430128826, 420472675, 411045284, 401840712, 392853196, 384077142, 375507123, 367137866, 358964257, 350981324, 343184244, 335568328, 328129023, 320861903, 313762670, 306827143, 300051261, 293431076, 286962747, 280642541, 274466826, 268432072, 262534841, 256771792]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 982).prefactor = (4834017356809923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 982).cutoff/(generalMeanRows 982).c)).2 =
    (30687212145493/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 982).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 982).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 982).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 982

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 982).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 982).criticalRate j.val*(generalMeanRows 982).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 982).c*(generalMeanRows 982).criticalPoint j.val)).2-
      (generalMeanRows 982).J/2-(generalMeanRows 982).error (generalMeanGrid j.val)+
      (generalMeanRows 982).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 982).c)).2-
      (generalMeanRows 982).J/2-(generalMeanRows 982).error 4 := by
  have he : (generalMeanRows 982).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 982) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 982)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0982

/-! Kernel-checked entropy margins for general spectral rectangle 983. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0983
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5423089362, 5245150584, 5074673315, 4911254434, 4754518660, 4604116105, 4459720100, 4321025257, 4187745727, 4059613633, 3936377669, 3817801822, 3703664224, 3593756105, 3487880846, 3385853107, 3287498046, 3192650588, 3101154764, 3012863106, 2927636085, 2845341598, 2765854491, 2689056122, 2614833956, 2543081190, 2473696403, 2406583235, 2341650086, 2278809840, 2217979599, 2159080448, 2102037225, 2046778309, 1993235430, 1941343475, 1891040323, 1842266682, 1794965934, 1749083997, 1704569190, 1661372109, 1619445507, 1578744185, 1539224888, 1500846205, 1463568479, 1427353720, 1392165519, 1357968975, 1324730620, 1292418349, 1261001356, 1230450072, 1200736107, 1171832193, 1143712133, 1116350753, 1089723852, 1063808160, 1038581294, 1014021720, 990108713, 966822322, 944143338, 922053258, 900534255, 879569150, 859141384, 839234992, 819834575, 800925279, 782492772, 764523219, 747003266, 729920018, 713261021, 697014241, 681168053, 665711217, 650632871, 635922510, 621569974, 607565433, 593899379, 580562607, 567546207, 554841554, 542440294, 530334335, 518515840, 506977212, 495711090, 484710337, 473968036, 463477477, 453232152, 443225749, 433452144, 423905393, 414579727, 405469545, 396569411, 387874044, 379378316, 371077246, 362965994, 355039857, 347294265, 339724775, 332327069, 325096947, 318030327, 311123237, 304371815, 297772304, 291321047, 285014487, 278849162, 272821701, 266928826]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 983).prefactor = (1195538871920363/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 983).cutoff/(generalMeanRows 983).c)).2 =
    (326039612147207/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 983).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 983).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 983).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 983

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 983).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 983).criticalRate j.val*(generalMeanRows 983).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 983).c*(generalMeanRows 983).criticalPoint j.val)).2-
      (generalMeanRows 983).J/2-(generalMeanRows 983).error (generalMeanGrid j.val)+
      (generalMeanRows 983).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 983).c)).2-
      (generalMeanRows 983).J/2-(generalMeanRows 983).error 4 := by
  have he : (generalMeanRows 983).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 983) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 983)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0983

/-! Kernel-checked entropy margins for general spectral rectangle 984. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0984
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5262798019, 5089811696, 4924127078, 4765346282, 4613099029, 4467040231, 4326847831, 4192220883, 4062877820, 3938554904, 3819004830, 3703995456, 3593308668, 3486739334, 3384094359, 3285191832, 3189860229, 3097937702, 3009271417, 2923716946, 2841137716, 2761404492, 2684394907, 2609993026, 2538088941, 2468578401, 2401362461, 2336347165, 2273443247, 2212565853, 2153634282, 2096571749, 2041305157, 1987764890, 1935884616, 1885601106, 1836854061, 1789585956, 1743741884, 1699269420, 1656118487, 1614241233, 1573591915, 1534126788, 1495804003, 1458583513, 1422426976, 1387297674, 1353160429, 1319981531, 1287728660, 1256370823, 1225878288, 1196222522, 1167376137, 1139312832, 1112007346, 1085435405, 1059573680, 1034399740, 1009892014, 986029751, 962792981, 940162483, 918119750, 896646956, 875726930, 855343124, 835479586, 816120939, 797252348, 778859506, 760928605, 743446319, 726399781, 709776568, 693564679, 677752517, 662328879, 647282933, 632604207, 618282572, 604308233, 590671710, 577363832, 564375720, 551698778, 539324681, 527245366, 515453023, 503940084, 492699211, 481723295, 471005442, 460538964, 450317378, 440334391, 430583901, 421059982, 411756885, 402669026, 393790986, 385117501, 376643456, 368363885, 360273962, 352368996, 344644428, 337095827, 329718885, 322509413, 315463336, 308576691, 301845624, 295266383, 288835320, 282548883, 276403614, 270396150, 264523213, 258781615]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 984).prefactor = (236206984854869/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 984).cutoff/(generalMeanRows 984).c)).2 =
    (339737135074603/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 984).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 984).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 984).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 984

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 984).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 984).criticalRate j.val*(generalMeanRows 984).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 984).c*(generalMeanRows 984).criticalPoint j.val)).2-
      (generalMeanRows 984).J/2-(generalMeanRows 984).error (generalMeanGrid j.val)+
      (generalMeanRows 984).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 984).c)).2-
      (generalMeanRows 984).J/2-(generalMeanRows 984).error 4 := by
  have he : (generalMeanRows 984).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 984) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 984)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0984

/-! Kernel-checked entropy margins for general spectral rectangle 985. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0985
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5345985204, 5176860142, 5014826566, 4859493895, 4710498902, 4567503306, 4430191643, 4298269347, 4171461039, 4049508985, 3932171703, 3819222713, 3710449393, 3605651950, 3504642478, 3407244106, 3313290208, 3222623697, 3135096362, 3050568270, 2968907209, 2889988183, 2813692942, 2739909543, 2668531957, 2599459693, 2532597456, 2467854830, 2405145978, 2344389374, 2285507539, 2228426809, 2173077111, 2119391757, 2067307248, 2016763097, 1967701658, 1920067968, 1873809601, 1828876529, 1785220990, 1742797370, 1701562084, 1661473474, 1622491702, 1584578662, 1547697885, 1511814458, 1476894945, 1442907312, 1409820854, 1377606135, 1346234920, 1315680119, 1285915730, 1256916787, 1228659311, 1201120262, 1174277494, 1148109716, 1122596449, 1097717991, 1073455379, 1049790357, 1026705343, 1004183400, 982208205, 960764025, 939835687, 919408559, 899468521, 880001946, 860995679, 842437014, 824313679, 806613818, 789325969, 772439051, 755942351, 739825503, 724078479, 708691574, 693655391, 678960832, 664599086, 650561616, 636840148, 623426665, 610313394, 597492795, 584957558, 572700588, 560715004, 548994123, 537531460, 526320718, 515355782, 504630709, 494139727, 483877229, 473837760, 464016022, 454406860, 445005263, 435806357, 426805399, 417997775, 409378994, 400944685, 392690595, 384612579, 376706603, 368968740, 361395162, 353982139, 346726040, 339623325, 332670542, 325864329, 319201407, 312678578]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 985).prefactor = (2330378611657859/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 985).cutoff/(generalMeanRows 985).c)).2 =
    (373719069371603/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 985).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 985).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 985).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 985

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 985).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 985).criticalRate j.val*(generalMeanRows 985).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 985).c*(generalMeanRows 985).criticalPoint j.val)).2-
      (generalMeanRows 985).J/2-(generalMeanRows 985).error (generalMeanGrid j.val)+
      (generalMeanRows 985).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 985).c)).2-
      (generalMeanRows 985).J/2-(generalMeanRows 985).error 4 := by
  have he : (generalMeanRows 985).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 985) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 985)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0985

/-! Kernel-checked entropy margins for general spectral rectangle 986. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0986
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5427880230, 5253918277, 5087280195, 4927562891, 4774391465, 4627416738, 4486313051, 4350776290, 4220522125, 4095284418, 3974813790, 3858876331, 3747252424, 3639735683, 3536131981, 3436258574, 3339943289, 3247023788, 3157346895, 3070767973, 2987150354, 2906364816, 2828289096, 2752807447, 2679810220, 2609193488, 2540858687, 2474712289, 2410665498, 2348633965, 2288537527, 2230299957, 2173848741, 2119114859, 2066032589, 2014539320, 1964575380, 1916083867, 1869010504, 1823303492, 1778913375, 1735792919, 1693896990, 1653182445, 1613608025, 1575134263, 1537723385, 1501339231, 1465947165, 1431514005, 1398007946, 1365398494, 1333656401, 1302753605, 1272663171, 1243359236, 1214816961, 1187012480, 1159922853, 1133526028, 1107800792, 1082726740, 1058284232, 1034454362, 1011218922, 988560376, 966461821, 944906970, 923880114, 903366107, 883350335, 863818694, 844757570, 826153819, 807994744, 790268079, 772961971, 756064962, 739565971, 723454286, 707719538, 692351699, 677341059, 662678221, 648354081, 634359824, 620686909, 607327059, 594272252, 581514708, 569046887, 556861471, 544951365, 533309680, 521929735, 510805039, 499929294, 489296381, 478900359, 468735453, 458796055, 449076712, 439572126, 430277144, 421186757, 412296091, 403600409, 395095099, 386775676, 378637773, 370677141, 362889643, 355271252, 347818047, 340526207, 333392013, 326411841, 319582160, 312899530, 306360598, 299962096]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 986).prefactor = (4804797862881839/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 986).cutoff/(generalMeanRows 986).c)).2 =
    (91827197752671/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 986).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 986).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 986).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 986

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 986).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 986).criticalRate j.val*(generalMeanRows 986).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 986).c*(generalMeanRows 986).criticalPoint j.val)).2-
      (generalMeanRows 986).J/2-(generalMeanRows 986).error (generalMeanGrid j.val)+
      (generalMeanRows 986).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 986).c)).2-
      (generalMeanRows 986).J/2-(generalMeanRows 986).error 4 := by
  have he : (generalMeanRows 986).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 986) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 986)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0986

/-! Kernel-checked entropy margins for general spectral rectangle 987. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0987
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5428632683, 5250182939, 5079309159, 4915594820, 4758652467, 4608121164, 4463664223, 4324967180, 4191735973, 4063695304, 3940587165, 3822169509, 3708215034, 3598510095, 3492853701, 3391056610, 3292940494, 3198337183, 3107087966, 3019042954, 2934060491, 2852006616, 2772754557, 2696184278, 2622182051, 2550640060, 2481456038, 2414532927, 2349778565, 2287105391, 2226430179, 2167673777, 2110760875, 2055619787, 2002182240, 1950383185, 1900160619, 1851455413, 1804211157, 1758374012, 1713892570, 1670717728, 1628802562, 1588102217, 1548573793, 1510176250, 1472870311, 1436618370, 1401384411, 1367133924, 1333833837, 1301452437, 1269959311, 1239325275, 1209522323, 1180523563, 1152303171, 1124836334, 1098099206, 1072068864, 1046723263, 1022041198, 998002261, 974586812, 951775939, 929551428, 907895730, 886791935, 866223741, 846175429, 826631838, 807578342, 789000824, 770885658, 753219687, 735990203, 719184931, 702792007, 686799966, 671197721, 655974552, 641120089, 626624301, 612477477, 598670220, 585193430, 572038296, 559196283, 546659122, 534418800, 522467550, 510797843, 499402378, 488274075, 477406065, 466791685, 456424468, 446298138, 436406603, 426743945, 417304421, 408082451, 399072614, 390269644, 381668423, 373263976, 365051469, 357026199, 349183597, 341519217, 334028734, 326707942, 319552749, 312559172, 305723335, 299041467, 292509894, 286125043, 279883432, 273781671, 267816458]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 987).prefactor = (4953290076484661/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 987).cutoff/(generalMeanRows 987).c)).2 =
    (354610207673557/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 987).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 987).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 987).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 987

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 987).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 987).criticalRate j.val*(generalMeanRows 987).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 987).c*(generalMeanRows 987).criticalPoint j.val)).2-
      (generalMeanRows 987).J/2-(generalMeanRows 987).error (generalMeanGrid j.val)+
      (generalMeanRows 987).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 987).c)).2-
      (generalMeanRows 987).J/2-(generalMeanRows 987).error 4 := by
  have he : (generalMeanRows 987).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 987) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 987)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0987

/-! Kernel-checked entropy margins for general spectral rectangle 988. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0988
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5512733157, 5329267560, 5153624519, 4985374112, 4824116385, 4669478726, 4521113529, 4378696100, 4241922785, 4110509285, 3984189131, 3862712314, 3745844041, 3633363602, 3525063343, 3420747730, 3320232493, 3223343842, 3129917750, 3039799293, 2952842045, 2868907522, 2787864664, 2709589364, 2633964027, 2560877162, 2490223012, 2421901197, 2355816394, 2291878035, 2230000028, 2170100491, 2112101515, 2055928930, 2001512100, 1948783718, 1897679625, 1848138635, 1800102374, 1753515125, 1708323688, 1664477243, 1621927228, 1580627217, 1540532813, 1501601539, 1463792744, 1427067506, 1391388549, 1356720159, 1323028105, 1290279569, 1258443076, 1227488425, 1197386635, 1168109881, 1139631439, 1111925638, 1084967808, 1058734234, 1033202112, 1008349508, 984155317, 960599226, 937661679, 915323844, 893567578, 872375402, 851730465, 831616525, 812017914, 792919520, 774306763, 756165569, 738482351, 721243988, 704437808, 688051567, 672073433, 656491969, 641296116, 626475181, 612018818, 597917020, 584160100, 570738684, 557643693, 544866338, 532398105, 520230745, 508356266, 496766922, 485455203, 474413829, 463635739, 453114085, 442842224, 432813709, 423022284, 413461877, 404126593, 395010708, 386108664, 377415060, 368924653, 360632346, 352533187, 344622363, 336895195, 329347136, 321973763, 314770775, 307733989, 300859338, 294142862, 287580711, 281169137, 274904492, 268783228, 262801887, 256957107]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 988).prefactor = (2553185719980073/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 988).cutoff/(generalMeanRows 988).c)).2 =
    (174160439382997/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 988).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 988).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 988).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 988

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 988).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 988).criticalRate j.val*(generalMeanRows 988).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 988).c*(generalMeanRows 988).criticalPoint j.val)).2-
      (generalMeanRows 988).J/2-(generalMeanRows 988).error (generalMeanGrid j.val)+
      (generalMeanRows 988).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 988).c)).2-
      (generalMeanRows 988).J/2-(generalMeanRows 988).error 4 := by
  have he : (generalMeanRows 988).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 988) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 988)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0988

/-! Kernel-checked entropy margins for general spectral rectangle 989. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0989
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5769361309, 5579711152, 5398112463, 5224122579, 5057329724, 4897350310, 4743826516, 4596424141, 4454830665, 4318753511, 4187918479, 4062068327, 3940961489, 3824370910, 3712082983, 3603896588, 3499622205, 3399081108, 3302104626, 3208533461, 3118217066, 3031013071, 2946786750, 2865410531, 2786763547, 2710731217, 2637204853, 2566081307, 2497262631, 2430655770, 2366172273, 2303728019, 2243242974, 2184640951, 2127849391, 2072799164, 2019424374, 1967662182, 1917452636, 1868738517, 1821465194, 1775580479, 1731034504, 1687779597, 1645770168, 1604962601, 1565315151, 1526787853, 1489342431, 1452942210, 1417552040, 1383138219, 1349668423, 1317111639, 1285438102, 1254619233, 1224627585, 1195436789, 1167021503, 1139357364, 1112420945, 1086189707, 1060641964, 1035756843, 1011514243, 987894808, 964879888, 942451512, 920592353, 899285707, 878515461, 858266070, 838522533, 819270366, 800495589, 782184696, 764324639, 746902812, 729907028, 713325507, 697146855, 681360050, 665954432, 650919682, 636245811, 621923149, 607942332, 594294289, 580970232, 567961645, 555260274, 542858116, 530747414, 518920642, 507370501, 496089908, 485071992, 474310082, 463797703, 453528568, 443496571, 433695783, 424120443, 414764954, 405623876, 396691924, 387963957, 379434982, 371100138, 362954702, 354994078, 347213796, 339609506, 332176977, 324912088, 317810832, 310869305, 304083708, 297450341, 290965602, 284625983]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 989).prefactor = (2632091890461833/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 989).cutoff/(generalMeanRows 989).c)).2 =
    (354610207673557/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 989).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 989).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 989).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 989

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 989).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 989).criticalRate j.val*(generalMeanRows 989).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 989).c*(generalMeanRows 989).criticalPoint j.val)).2-
      (generalMeanRows 989).J/2-(generalMeanRows 989).error (generalMeanGrid j.val)+
      (generalMeanRows 989).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 989).c)).2-
      (generalMeanRows 989).J/2-(generalMeanRows 989).error 4 := by
  have he : (generalMeanRows 989).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 989) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 989)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0989

/-! Kernel-checked entropy margins for general spectral rectangle 990. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0990
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5947663343, 5752152050, 5564941056, 5385574017, 5213626432, 5048702855, 4890434411, 4738476567, 4592507147, 4452224530, 4317346043, 4187606494, 4062756851, 3942563041, 3826804858, 3715274964, 3607777983, 3504129665, 3404156125, 3307693144, 3214585523, 3124686490, 3037857155, 2953966005, 2872888438, 2794506329, 2718707634, 2645386015, 2574440499, 2505775154, 2439298795, 2374924703, 2312570368, 2252157250, 2193610548, 2136858995, 2081834658, 2028472755, 1976711484, 1926491856, 1877757551, 1830454770, 1784532102, 1739940403, 1696632673, 1654563948, 1613691194, 1573973212, 1535370539, 1497845369, 1461361466, 1425884087, 1391379907, 1357816957, 1325164549, 1293393223, 1262474684, 1232381747, 1203088287, 1174569188, 1146800299, 1119758385, 1093421090, 1067766894, 1042775077, 1018425684, 994699488, 971577963, 949043247, 927078120, 905665970, 884790772, 864437060, 844589906, 825234895, 806358103, 787946082, 769985833, 752464795, 735370822, 718692169, 702417474, 686535745, 671036346, 655908979, 641143676, 626730782, 612660946, 598925109, 585514492, 572420585, 559635139, 547150156, 534957877, 523050779, 511421560, 500063135, 488968629, 478131365, 467544862, 457202827, 447099146, 437227880, 427583259, 418159677, 408951682, 399953978, 391161415, 382568983, 374171812, 365965165, 357944434, 350105133, 342442902, 334953492, 327632771, 320476716, 313481411, 306643040, 299957891, 293422345]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 990).prefactor = (1085374662034223/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 990).cutoff/(generalMeanRows 990).c)).2 =
    (354610207673557/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 990).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 990).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 990).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 990

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 990).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 990).criticalRate j.val*(generalMeanRows 990).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 990).c*(generalMeanRows 990).criticalPoint j.val)).2-
      (generalMeanRows 990).J/2-(generalMeanRows 990).error (generalMeanGrid j.val)+
      (generalMeanRows 990).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 990).c)).2-
      (generalMeanRows 990).J/2-(generalMeanRows 990).error 4 := by
  have he : (generalMeanRows 990).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 990) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 990)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0990

/-! Kernel-checked entropy margins for general spectral rectangle 991. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0991
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7464472592, 7248735420, 7041236966, 6841556867, 6649303505, 6464111417, 6285638991, 6113566426, 5947593907, 5787439975, 5632840070, 5483545209, 5339320810, 5199945611, 5065210706, 4934918660, 4808882707, 4686926017, 4568881030, 4454588839, 4343898630, 4236667167, 4132758313, 4032042597, 3934396804, 3839703602, 3747851198, 3658733014, 3572247389, 3488297302, 3406790114, 3327637325, 3250754353, 3176060320, 3103477862, 3032932936, 2964354658, 2897675136, 2832829320, 2769754858, 2708391966, 2648683300, 2590573837, 2534010767, 2478943381, 2425322979, 2373102772, 2322237794, 2272684821, 2224402285, 2177350209, 2131490126, 2086785018, 2043199250, 2000698510, 1959249752, 1918821137, 1879381990, 1840902742, 1803354887, 1766710939, 1730944385, 1696029648, 1661942050, 1628657770, 1596153813, 1564407978, 1533398821, 1503105630, 1473508393, 1444587771, 1416325071, 1388702223, 1361701755, 1335306767, 1309500913, 1284268380, 1259593862, 1235462550, 1211860104, 1188772643, 1166186722, 1144089322, 1122467828, 1101310020, 1080604054, 1060338451, 1040502084, 1021084162, 1002074224, 983462121, 965238010, 947392340, 929915842, 912799522, 896034649, 879612746, 863525581, 847765161, 832323721, 817193719, 802367826, 787838921, 773600080, 759644577, 745965869, 732557596, 719413573, 706527783, 693894373, 681507650, 669362073, 657452250, 645772932, 634319010, 623085510, 612067587, 601260526, 590659731, 580260726, 570059151]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 991).prefactor = (5107890788590123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 991).cutoff/(generalMeanRows 991).c)).2 =
    (69570779728617/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 991).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 991).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 991).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 991

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 991).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 991).criticalRate j.val*(generalMeanRows 991).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 991).c*(generalMeanRows 991).criticalPoint j.val)).2-
      (generalMeanRows 991).J/2-(generalMeanRows 991).error (generalMeanGrid j.val)+
      (generalMeanRows 991).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 991).c)).2-
      (generalMeanRows 991).J/2-(generalMeanRows 991).error 4 := by
  have he : (generalMeanRows 991).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 991) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 991)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0991

/-! Kernel-checked entropy margins for general spectral rectangle 992. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0992
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7071281766, 6858811223, 6654587791, 6458189183, 6269221922, 6087318749, 5912136329, 5743353213, 5580668017, 5423797792, 5272476562, 5126454011, 4985494295, 4849374969, 4717886012, 4590828946, 4468016027, 4349269515, 4234420996, 4123310774, 4015787301, 3911706656, 3810932076, 3713333505, 3618787193, 3527175316, 3438385629, 3352311143, 3268849821, 3187904300, 3109381634, 3033193046, 2959253705, 2887482512, 2817801906, 2750137675, 2684418784, 2620577213, 2558547803, 2498268115, 2439678290, 2382720930, 2327340969, 2273485569, 2221104010, 2170147589, 2120569525, 2072324874, 2025370441, 1979664699, 1935167715, 1891841080, 1849647839, 1808552425, 1768520602, 1729519404, 1691517080, 1654483044, 1618387824, 1583203014, 1548901228, 1515456063, 1482842050, 1451034622, 1420010074, 1389745529, 1360218903, 1331408873, 1303294849, 1275856943, 1249075940, 1222933274, 1197411002, 1172491778, 1148158832, 1124395945, 1101187434, 1078518123, 1056373330, 1034738848, 1013600924, 992946244, 972761917, 953035460, 933754780, 914908164, 896484262, 878472074, 860860938, 843640521, 826800802, 810332064, 794224883, 778470116, 763058894, 747982612, 733232915, 718801698, 704681089, 690863448, 677341352, 664107596, 651155178, 638477297, 626067343, 613918896, 602025712, 590381724, 578981033, 567817904, 556886757, 546182168, 535698860, 525431698, 515375686, 505525964, 495877800, 486426589, 477167847, 468097210, 459210426]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 992).prefactor = (511212072459053/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 992).cutoff/(generalMeanRows 992).c)).2 =
    (134600707193117/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 992).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 992).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 992).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 992

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 992).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 992).criticalRate j.val*(generalMeanRows 992).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 992).c*(generalMeanRows 992).criticalPoint j.val)).2-
      (generalMeanRows 992).J/2-(generalMeanRows 992).error (generalMeanGrid j.val)+
      (generalMeanRows 992).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 992).c)).2-
      (generalMeanRows 992).J/2-(generalMeanRows 992).error 4 := by
  have he : (generalMeanRows 992).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 992) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 992)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0992

/-! Kernel-checked entropy margins for general spectral rectangle 993. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0993
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6941852812, 6744152178, 6554134115, 6371398258, 6195571729, 6026306673, 5863278087, 5706181880, 5554733136, 5408664571, 5267725129, 5131678736, 5000303162, 4873388994, 4750738706, 4632165814, 4517494100, 4406556911, 4299196512, 4195263499, 4094616249, 3997120429, 3902648529, 3811079443, 3722298075, 3636194976, 3552666009, 3471612034, 3392938624, 3316555790, 3242377733, 3170322609, 3100312311, 3032272267, 2966131246, 2901821183, 2839277008, 2778436494, 2719240108, 2661630871, 2605554231, 2550957939, 2497791938, 2446008249, 2395560873, 2346405696, 2298500394, 2251804352, 2206278579, 2161885635, 2118589556, 2076355788, 2035151120, 1994943623, 1955702596, 1917398503, 1880002927, 1843488519, 1807828949, 1772998865, 1738973845, 1705730363, 1673245744, 1641498134, 1610466460, 1580130400, 1550470351, 1521467396, 1493103282, 1465360386, 1438221692, 1411670767, 1385691736, 1360269261, 1335388517, 1311035173, 1287195374, 1263855719, 1241003246, 1218625413, 1196710083, 1175245507, 1154220312, 1133623481, 1113444346, 1093672572, 1074298143, 1055311351, 1036702787, 1018463327, 1000584123, 983056592, 965872406, 949023485, 932501987, 916300298, 900411025, 884826989, 869541218, 854546935, 839837559, 825406689, 811248108, 797355768, 783723788, 770346450, 757218190, 744333594, 731687395, 719274465, 707089814, 695128580, 683386033, 671857562, 660538678, 649425006, 638512282, 627796352, 617273166, 606938775, 596789329]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 993).prefactor = (4851087689391467/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 993).cutoff/(generalMeanRows 993).c)).2 =
    (32419157065511/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 993).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 993).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 993).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 993

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 993).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 993).criticalRate j.val*(generalMeanRows 993).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 993).c*(generalMeanRows 993).criticalPoint j.val)).2-
      (generalMeanRows 993).J/2-(generalMeanRows 993).error (generalMeanGrid j.val)+
      (generalMeanRows 993).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 993).c)).2-
      (generalMeanRows 993).J/2-(generalMeanRows 993).error 4 := by
  have he : (generalMeanRows 993).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 993) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 993)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0993

/-! Kernel-checked entropy margins for general spectral rectangle 994. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0994
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6710133902, 6515957921, 6329404137, 6150072931, 5977592139, 5811614604, 5651816013, 5497892960, 5349561221, 5206554206, 5068621568, 4935527948, 4807051843, 4682984581, 4563129389, 4447300544, 4335322603, 4227029696, 4122264881, 4020879552, 3922732893, 3827691380, 3735628321, 3646423426, 3559962418, 3476136666, 3394842852, 3315982653, 3239462453, 3165193072, 3093089516, 3023070739, 2955059425, 2888981785, 2824767365, 2762348867, 2701661980, 2642645224, 2585239803, 2529389466, 2475040376, 2422140990, 2370641943, 2320495936, 2271657640, 2224083596, 2177732126, 2132563243, 2088538577, 2045621293, 2003776021, 1962968785, 1923166944, 1884339124, 1846455164, 1809486059, 1773403910, 1738181873, 1703794111, 1670215751, 1637422842, 1605392313, 1574101936, 1543530290, 1513656726, 1484461332, 1455924907, 1428028925, 1400755511, 1374087412, 1348007971, 1322501106, 1297551280, 1273143486, 1249263221, 1225896465, 1203029667, 1180649721, 1158743950, 1137300091, 1116306277, 1095751022, 1075623207, 1055912063, 1036607162, 1017698402, 999175993, 981030448, 963252571, 945833445, 928764422, 912037116, 895643388, 879575342, 863825314, 848385864, 833249766, 818410007, 803859770, 789592434, 775601567, 761880915, 748424400, 735226111, 722280302, 709581381, 697123912, 684902602, 672912304, 661148003, 649604822, 638278010, 627162940, 616255106, 605550118, 595043698, 584731679, 574609999, 564674696, 554921911, 545347878]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 994).prefactor = (151055334387707/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 994).cutoff/(generalMeanRows 994).c)).2 =
    (642345529333/1953125000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 994).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 994).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 994).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 994

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 994).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 994).criticalRate j.val*(generalMeanRows 994).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 994).c*(generalMeanRows 994).criticalPoint j.val)).2-
      (generalMeanRows 994).J/2-(generalMeanRows 994).error (generalMeanGrid j.val)+
      (generalMeanRows 994).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 994).c)).2-
      (generalMeanRows 994).J/2-(generalMeanRows 994).error 4 := by
  have he : (generalMeanRows 994).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 994) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 994)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0994

/-! Kernel-checked entropy margins for general spectral rectangle 995. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0995
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6528172872, 6337867470, 6155095081, 5979457914, 5810585558, 5648132556, 5491776246, 5341214838, 5196165691, 5056363774, 4921560277, 4791521360, 4666027023, 4544870083, 4427855241, 4314798235, 4205525072, 4099871319, 3997681455, 3898808285, 3803112388, 3710461624, 3620730664, 3533800572, 3449558405, 3367896852, 3288713893, 3211912491, 3137400293, 3065089367, 2994895944, 2926740185, 2860545962, 2796240652, 2733754947, 2673022672, 2613980620, 2556568395, 2500728261, 2446405005, 2393545810, 2342100128, 2292019568, 2243257786, 2195770384, 2149514814, 2104450286, 2060537684, 2017739484, 1976019679, 1935343704, 1895678373, 1856991809, 1819253386, 1782433672, 1746504370, 1711438272, 1677209204, 1643791984, 1611162376, 1579297045, 1548173524, 1517770168, 1488066124, 1459041296, 1430676309, 1402952480, 1375851792, 1349356860, 1323450907, 1298117741, 1273341725, 1249107762, 1225401265, 1202208141, 1179514768, 1157307980, 1135575044, 1114303647, 1093481876, 1073098205, 1053141475, 1033600888, 1014465986, 995726638, 977373033, 959395664, 941785314, 924533052, 907630215, 891068404, 874839470, 858935507, 843348844, 828072032, 813097842, 798419253, 784029447, 769921798, 756089870, 742527408, 729228331, 716186729, 703396853, 690853112, 678550068, 666482429, 654645047, 643032908, 631641134, 620464975, 609499804, 598741115, 588184520, 577825741, 567660610, 557685066, 547895148, 538286996, 528856845, 519601025]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 995).prefactor = (2403134730694089/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 995).cutoff/(generalMeanRows 995).c)).2 =
    (67665216318003/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 995).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 995).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 995).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 995

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 995).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 995).criticalRate j.val*(generalMeanRows 995).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 995).c*(generalMeanRows 995).criticalPoint j.val)).2-
      (generalMeanRows 995).J/2-(generalMeanRows 995).error (generalMeanGrid j.val)+
      (generalMeanRows 995).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 995).c)).2-
      (generalMeanRows 995).J/2-(generalMeanRows 995).error 4 := by
  have he : (generalMeanRows 995).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 995) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 995)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0995

/-! Kernel-checked entropy margins for general spectral rectangle 996. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0996
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6250118281, 6064285755, 5885892123, 5714541993, 5549867232, 5391524559, 5239193397, 5092573967, 4951385572, 4815365068, 4684265479, 4557854753, 4435914638, 4318239655, 4204636177, 4094921579, 3988923471, 3886478994, 3787434171, 3691643318, 3598968502, 3509279037, 3422451026, 3338366932, 3256915187, 3177989826, 3101490152, 3027320418, 2955389539, 2885610821, 2817901709, 2752183550, 2688381376, 2626423699, 2566242318, 2507772142, 2450951021, 2395719588, 2342021115, 2289801371, 2239008496, 2189592874, 2141507024, 2094705487, 2049144727, 2004783036, 1961580441, 1919498620, 1878500822, 1838551792, 1799617697, 1761666060, 1724665695, 1688586647, 1653400133, 1619078492, 1585595127, 1552924462, 1521041894, 1489923746, 1459547231, 1429890408, 1400932146, 1372652090, 1345030624, 1318048842, 1291688515, 1265932063, 1240762529, 1216163548, 1192119329, 1168614624, 1145634709, 1123165362, 1101192845, 1079703877, 1058685624, 1038125675, 1018012026, 998333068, 979077566, 960234646, 941793784, 923744787, 906077786, 888783217, 871851815, 855274602, 839042872, 823148186, 807582357, 792337446, 777405749, 762779790, 748452313, 734416272, 720664825, 707191329, 693989328, 681052550, 668374901, 655950455, 643773451, 631838290, 620139523, 608671851, 597430118, 586409306, 575604533, 565011045, 554624213, 544439530, 534452606, 524659165, 515055041, 505636173, 496398606, 487338481, 478452040, 469735616, 461185633]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 996).prefactor = (47697369695181/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 996).cutoff/(generalMeanRows 996).c)).2 =
    (341891147754511/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 996).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 996).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 996).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 996

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 996).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 996).criticalRate j.val*(generalMeanRows 996).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 996).c*(generalMeanRows 996).criticalPoint j.val)).2-
      (generalMeanRows 996).J/2-(generalMeanRows 996).error (generalMeanGrid j.val)+
      (generalMeanRows 996).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 996).c)).2-
      (generalMeanRows 996).J/2-(generalMeanRows 996).error 4 := by
  have he : (generalMeanRows 996).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 996) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 996)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0996

/-! Kernel-checked entropy margins for general spectral rectangle 997. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0997
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5854178231, 5663665741, 5480983448, 5305717181, 5137481107, 4975915234, 4820683189, 4671470239, 4527981514, 4389940420, 4257087205, 4129177669, 4005981994, 3887283688, 3772878618, 3662574137, 3556188284, 3453549053, 3354493721, 3258868240, 3166526665, 3077330638, 2991148911, 2907856898, 2827336270, 2749474578, 2674164896, 2601305500, 2530799564, 2462554876, 2396483579, 2332501924, 2270530044, 2210491738, 2152314271, 2095928193, 2041267157, 1988267760, 1936869387, 1887014067, 1838646340, 1791713125, 1746163602, 1701949102, 1659022994, 1617340593, 1576859057, 1537537305, 1499335927, 1462217110, 1426144555, 1391083415, 1357000220, 1323862817, 1291640310, 1260303000, 1229822333, 1200170850, 1171322132, 1143250762, 1115932275, 1089343118, 1063460611, 1038262910, 1013728968, 989838504, 966571969, 943910517, 921835973, 900330805, 879378101, 858961541, 839065371, 819674384, 800773894, 782349719, 764388156, 746875968, 729800361, 713148966, 696909827, 681071382, 665622447, 650552204, 635850184, 621506258, 607510619, 593853773, 580526530, 567519985, 554825515, 542434766, 530339640, 518532293, 507005119, 495750742, 484762015, 474032002, 463553976, 453321414, 443327983, 433567539, 424034118, 414721932, 405625359, 396738941, 388057378, 379575522, 371288370, 363191062, 355278877, 347547225, 339991644, 332607799, 325391473, 318338566, 311445090, 304707168, 298121026, 291682996, 285389505]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 997).prefactor = (4959676953466319/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 997).cutoff/(generalMeanRows 997).c)).2 =
    (294424610515587/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 997).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 997).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 997).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 997

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 997).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 997).criticalRate j.val*(generalMeanRows 997).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 997).c*(generalMeanRows 997).criticalPoint j.val)).2-
      (generalMeanRows 997).J/2-(generalMeanRows 997).error (generalMeanGrid j.val)+
      (generalMeanRows 997).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 997).c)).2-
      (generalMeanRows 997).J/2-(generalMeanRows 997).error 4 := by
  have he : (generalMeanRows 997).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 997) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 997)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0997

/-! Kernel-checked entropy margins for general spectral rectangle 998. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0998
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5673257040, 5487828038, 5310081001, 5139606289, 4976022382, 4818973411, 4668126951, 4523172064, 4383817536, 4249790303, 4120834026, 3996707809, 3877185039, 3762052335, 3651108587, 3544164088, 3441039735, 3341566307, 3245583793, 3152940783, 3063493906, 2977107311, 2893652193, 2813006347, 2735053766, 2659684260, 2586793109, 2516280735, 2448052405, 2382017946, 2318091486, 2256191210, 2196239133, 2138160886, 2081885520, 2027345320, 1974475629, 1923214688, 1873503480, 1825285589, 1778507066, 1733116299, 1689063898, 1646302578, 1604787059, 1564473964, 1525321724, 1487290491, 1450342055, 1414439766, 1379548455, 1345634369, 1312665103, 1280609535, 1249437768, 1219121074, 1189631839, 1160943515, 1133030568, 1105868437, 1079433486, 1053702967, 1028654980, 1004268433, 980523013, 957399146, 934877969, 912941298, 891571603, 870751973, 850466100, 830698245, 811433220, 792656363, 774353518, 756511012, 739115640, 722154641, 705615685, 689486852, 673756619, 658413842, 643447745, 628847900, 614604219, 600706938, 587146607, 573914075, 561000482, 548397246, 536096053, 524088850, 512367830, 500925428, 489754310, 478847363, 468197693, 457798610, 447643625, 437726443, 428040954, 418581228, 409341510, 400316211, 391499905, 382887321, 374473340, 366252990, 358221439, 350373992, 342706086, 335213284, 327891275, 320735867, 313742982, 306908656, 300229032, 293700358, 287318985, 281081360, 274984027]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 998).prefactor = (980605053875979/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 998).cutoff/(generalMeanRows 998).c)).2 =
    (306991417176511/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 998).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 998).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 998).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 998

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 998).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 998).criticalRate j.val*(generalMeanRows 998).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 998).c*(generalMeanRows 998).criticalPoint j.val)).2-
      (generalMeanRows 998).J/2-(generalMeanRows 998).error (generalMeanGrid j.val)+
      (generalMeanRows 998).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 998).c)).2-
      (generalMeanRows 998).J/2-(generalMeanRows 998).error 4 := by
  have he : (generalMeanRows 998).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 998) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 998)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0998

/-! Kernel-checked entropy margins for general spectral rectangle 999. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0999
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5579242041, 5398613158, 5225490759, 5059470988, 4900177860, 4747260810, 4600392515, 4459266949, 4323597638, 4193116097, 4067570418, 3946723997, 3830354382, 3718252227, 3610220339, 3506072816, 3405634252, 3308739016, 3215230590, 3124960957, 3037790046, 2953585215, 2872220779, 2793577565, 2717542516, 2644008309, 2572873008, 2504039745, 2437416418, 2372915409, 2310453331, 2249950781, 2191332114, 2134525237, 2079461408, 2026075052, 1974303592, 1924087282, 1875369062, 1828094412, 1782211218, 1737669650, 1694422042, 1652422783, 1611628211, 1571996516, 1533487647, 1496063226, 1459686463, 1424322084, 1389936252, 1356496499, 1323971664, 1292331827, 1261548256, 1231593344, 1202440563, 1174064412, 1146440370, 1119544852, 1093355168, 1067849478, 1043006762, 1018806775, 995230022, 972257716, 949871755, 928054689, 906789692, 886060537, 865851568, 846147679, 826934290, 808197325, 789923191, 772098760, 754711346, 737748691, 721198949, 705050665, 689292762, 673914525, 658905591, 644255929, 629955831, 615995900, 602367036, 589060427, 576067535, 563380089, 550990074, 538889721, 527071498, 515528102, 504252451, 493237674, 482477106, 471964280, 461692918, 451656927, 441850391, 432267566, 422902874, 413750894, 404806364, 396064166, 387519329, 379167022, 371002546, 363021336, 355218949, 347591066, 340133487, 332842123, 325712999, 318742245, 311926094, 305260882, 298743040, 292369093, 286135659]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 999).prefactor = (968009212210663/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 999).cutoff/(generalMeanRows 999).c)).2 =
    (327119830434199/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 999).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 999).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 999).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 999

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 999).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 999).criticalRate j.val*(generalMeanRows 999).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 999).c*(generalMeanRows 999).criticalPoint j.val)).2-
      (generalMeanRows 999).J/2-(generalMeanRows 999).error (generalMeanGrid j.val)+
      (generalMeanRows 999).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 999).c)).2-
      (generalMeanRows 999).J/2-(generalMeanRows 999).error 4 := by
  have he : (generalMeanRows 999).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 999) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 999)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0999

/-! Kernel-checked entropy margins for general spectral rectangle 1000. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1000
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5571423124, 5395383497, 5226647439, 5064818037, 4909525968, 4760427078, 4617200221, 4479545334, 4347181706, 4219846429, 4097292994, 3979290031, 3865620163, 3756078967, 3650474032, 3548624094, 3450358255, 3355515259, 3263942840, 3175497111, 3090042012, 3007448798, 2927595565, 2850366820, 2775653071, 2703350460, 2633360415, 2565589333, 2499948278, 2436352707, 2374722213, 2314980282, 2257054074, 2200874211, 2146374585, 2093492172, 2042166865, 1992341312, 1943960770, 1896972959, 1851327939, 1806977977, 1763877439, 1721982679, 1681251931, 1641645222, 1603124275, 1565652423, 1529194534, 1493716929, 1459187313, 1425574709, 1392849391, 1360982826, 1329947615, 1299717443, 1270267021, 1241572047, 1213609153, 1186355863, 1159790556, 1133892425, 1108641436, 1084018301, 1060004440, 1036581949, 1013733573, 991442678, 969693219, 948469721, 927757251, 907541397, 887808244, 868544353, 849736743, 831372873, 813440620, 795928265, 778824478, 762118296, 745799116, 729856677, 714281046, 699062607, 684192046, 669660344, 655458760, 641578825, 628012330, 614751316, 601788064, 589115089, 576725129, 564611136, 552766271, 541183895, 529857562, 518781012, 507948165, 497353114, 486990119, 476853603, 466938143, 457238470, 447749457, 438466120, 429383611, 420497213, 411802337, 403294517, 394969405, 386822771, 378850493, 371048562, 363413069, 355940209, 348626276, 341467657, 334460833, 327602374, 320888937]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1000).prefactor = (4771596813378881/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1000).cutoff/(generalMeanRows 1000).c)).2 =
    (354670874400909/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1000).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1000).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1000).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1000

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1000).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1000).criticalRate j.val*(generalMeanRows 1000).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1000).c*(generalMeanRows 1000).criticalPoint j.val)).2-
      (generalMeanRows 1000).J/2-(generalMeanRows 1000).error (generalMeanGrid j.val)+
      (generalMeanRows 1000).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1000).c)).2-
      (generalMeanRows 1000).J/2-(generalMeanRows 1000).error 4 := by
  have he : (generalMeanRows 1000).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1000) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1000)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1000

/-! Kernel-checked entropy margins for general spectral rectangle 1001. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1001
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5401638453, 5231126771, 5067728783, 4911054268, 4760740292, 4616448815, 4477864553, 4344693076, 4216659088, 4093504900, 3974989033, 3860884970, 3750980024, 3645074301, 3542979768, 3444519400, 3349526394, 3257843463, 3169322178, 3083822369, 3001211573, 2921364529, 2844162706, 2769493874, 2697251703, 2627335395, 2559649340, 2494102801, 2430609616, 2369087926, 2309459921, 2251651599, 2195592551, 2141215748, 2088457353, 2037256538, 1987555319, 1939298396, 1892433007, 1846908789, 1802677649, 1759693642, 1717912859, 1677293318, 1637794863, 1599379070, 1562009160, 1525649912, 1490267586, 1455829848, 1422305700, 1389665414, 1357880471, 1326923498, 1296768219, 1267389395, 1238762782, 1210865076, 1183673877, 1157167640, 1131325639, 1106127930, 1081555313, 1057589299, 1034212077, 1011406487, 989155989, 967444635, 946257043, 925578376, 905394313, 885691032, 866455186, 847673882, 829334666, 811425501, 793934753, 776851169, 760163868, 743862324, 727936349, 712376082, 697171975, 682314784, 667795552, 653605601, 639736522, 626180163, 612928618, 599974224, 587309544, 574927363, 562820680, 550982700, 539406824, 528086647, 517015944, 506188673, 495598958, 485241092, 475109528, 465198871, 455503877, 446019445, 436740615, 427662559, 418780582, 410090112, 401586702, 393266021, 385123853, 377156091, 369358736, 361727895, 354259771, 346950669, 339796984, 332795205, 325941911, 319233764, 312667511]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1001).prefactor = (234923108055817/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1001).cutoff/(generalMeanRows 1001).c)).2 =
    (92617567826953/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1001).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1001).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1001).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1001

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1001).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1001).criticalRate j.val*(generalMeanRows 1001).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1001).c*(generalMeanRows 1001).criticalPoint j.val)).2-
      (generalMeanRows 1001).J/2-(generalMeanRows 1001).error (generalMeanGrid j.val)+
      (generalMeanRows 1001).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1001).c)).2-
      (generalMeanRows 1001).J/2-(generalMeanRows 1001).error 4 := by
  have he : (generalMeanRows 1001).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1001) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1001)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1001

/-! Kernel-checked entropy margins for general spectral rectangle 1002. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1002
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5490548737, 5314990377, 5146786312, 4985533395, 4830856635, 4682406731, 4539857867, 4402905747, 4271265826, 4144671731, 4022873820, 3905637901, 3792744053, 3683985569, 3579167985, 3478108203, 3380633683, 3286581713, 3195798726, 3108139688, 3023467529, 2941652612, 2862572261, 2786110305, 2712156672, 2640607008, 2571362319, 2504328648, 2439416770, 2376541906, 2315623464, 2256584792, 2199352950, 2143858498, 2090035294, 2037820314, 1987153472, 1937977461, 1890237601, 1843881694, 1798859893, 1755124575, 1712630225, 1671333321, 1631192235, 1592167133, 1554219883, 1517313970, 1481414412, 1446487683, 1412501645, 1379425473, 1347229597, 1315885638, 1285366348, 1255645561, 1226698139, 1198499922, 1171027686, 1144259095, 1118172664, 1092747717, 1067964352, 1043803404, 1020246415, 997275601, 974873821, 953024548, 931711849, 910920348, 890635214, 870842128, 851527268, 832677284, 814279279, 796320794, 778789784, 761674606, 744963999, 728647072, 712713286, 697152443, 681954671, 667110410, 652610403, 638445682, 624607557, 611087608, 597877669, 584969827, 572356405, 560029956, 547983257, 536209297, 524701272, 513452575, 502456793, 491707696, 481199232, 470925524, 460880859, 451059683, 441456601, 432066366, 422883874, 413904163, 405122407, 396533909, 388134100, 379918534, 371882881, 364022928, 356334574, 348813824, 341456789, 334259678, 327218801, 320330563, 313591459, 306998076, 300547084]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1002).prefactor = (1212102989455877/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1002).cutoff/(generalMeanRows 1002).c)).2 =
    (91040275528637/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1002).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1002).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1002).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1002

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1002).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1002).criticalRate j.val*(generalMeanRows 1002).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1002).c*(generalMeanRows 1002).criticalPoint j.val)).2-
      (generalMeanRows 1002).J/2-(generalMeanRows 1002).error (generalMeanGrid j.val)+
      (generalMeanRows 1002).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1002).c)).2-
      (generalMeanRows 1002).J/2-(generalMeanRows 1002).error 4 := by
  have he : (generalMeanRows 1002).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1002) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1002)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1002

/-! Kernel-checked entropy margins for general spectral rectangle 1003. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1003
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5498236656, 5317974253, 5145327330, 4979878841, 4821240800, 4669051736, 4522974422, 4382693846, 4247915394, 4118363209, 3993778721, 3873919314, 3758557115, 3647477903, 3540480110, 3437373913, 3337980404, 3242130830, 3149665901, 3060435146, 2974296332, 2891114919, 2810763562, 2733121656, 2658074905, 2585514930, 2515338906, 2447449224, 2381753175, 2318162658, 2256593910, 2196967253, 2139206856, 2083240517, 2028999458, 1976418131, 1925434039, 1875987571, 1828021840, 1781482539, 1736317801, 1692478069, 1649915977, 1608586233, 1568445510, 1529452348, 1491567060, 1454751636, 1418969665, 1384186251, 1350367941, 1317482653, 1285499610, 1254389273, 1224123287, 1194674422, 1166016520, 1138124443, 1110974028, 1084542041, 1058806134, 1033744804, 1009337355, 985563864, 962405142, 939842706, 917858744, 896436090, 875558190, 855209082, 835373366, 816036181, 797183187, 778800534, 760874850, 743393217, 726343154, 709712598, 693489888, 677663748, 662223272, 647157911, 632457456, 618112027, 604112059, 590448289, 577111749, 564093749, 551385870, 538979952, 526868086, 515042605, 503496072, 492221276, 481211220, 470459116, 459958375, 449702605, 439685596, 429901321, 420343927, 411007727, 401887199, 392976974, 384271838, 375766721, 367456695, 359336969, 351402885, 343649912, 336073642, 328669790, 321434183, 314362763, 307451580, 300696791, 294094651, 287641519, 281333846, 275168178, 269141151]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1003).prefactor = (2501573675244919/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1003).cutoff/(generalMeanRows 1003).c)).2 =
    (87915234837579/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1003).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1003).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1003).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1003

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1003).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1003).criticalRate j.val*(generalMeanRows 1003).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1003).c*(generalMeanRows 1003).criticalPoint j.val)).2-
      (generalMeanRows 1003).J/2-(generalMeanRows 1003).error (generalMeanGrid j.val)+
      (generalMeanRows 1003).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1003).c)).2-
      (generalMeanRows 1003).J/2-(generalMeanRows 1003).error 4 := by
  have he : (generalMeanRows 1003).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1003) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1003)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1003

/-! Kernel-checked entropy margins for general spectral rectangle 1004. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1004
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5589652629, 5404141596, 5226501928, 5056302709, 4893143017, 4736649296, 4586473014, 4442288572, 4303791425, 4170696397, 4042736155, 3919659840, 3801231821, 3687230558, 3577447583, 3471686557, 3369762413, 3271500579, 3176736253, 3085313748, 2997085887, 2911913444, 2829664628, 2750214612, 2673445093, 2599243882, 2527504533, 2458125993, 2391012275, 2326072156, 2263218904, 2202370005, 2143446932, 2086374908, 2031082699, 1977502414, 1925569320, 1875221669, 1826400534, 1779049660, 1733115316, 1688546164, 1645293136, 1603309308, 1562549797, 1522971651, 1484533752, 1447196726, 1410922850, 1375675977, 1341421450, 1308126036, 1275757854, 1244286308, 1213682029, 1183916814, 1154963570, 1126796268, 1099389885, 1072720362, 1046764562, 1021500224, 996905924, 972961038, 949645709, 926940807, 904827904, 883289236, 862307683, 841866731, 821950456, 802543492, 783631010, 765198695, 747232728, 729719758, 712646891, 696001666, 679772040, 663946369, 648513395, 633462229, 618782337, 604463525, 590495927, 576869992, 563576473, 550606413, 537951136, 525602237, 513551570, 501791239, 490313590, 479111201, 468176875, 457503628, 447084687, 436913479, 426983626, 417288934, 407823392, 398581163, 389556577, 380744128, 372138466, 363734393, 355526859, 347510953, 339681905, 332035074, 324565950, 317270146, 310143395, 303181547, 296380566, 289736522, 283245593, 276904058, 270708298, 264654788, 258740096]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1004).prefactor = (5162821069757109/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1004).cutoff/(generalMeanRows 1004).c)).2 =
    (69093793820479/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1004).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1004).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1004).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1004

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1004).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1004).criticalRate j.val*(generalMeanRows 1004).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1004).c*(generalMeanRows 1004).criticalPoint j.val)).2-
      (generalMeanRows 1004).J/2-(generalMeanRows 1004).error (generalMeanGrid j.val)+
      (generalMeanRows 1004).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1004).c)).2-
      (generalMeanRows 1004).J/2-(generalMeanRows 1004).error 4 := by
  have he : (generalMeanRows 1004).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1004) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1004)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1004

/-! Kernel-checked entropy margins for general spectral rectangle 1005. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1005
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5768044462, 5576612908, 5393303931, 5217672863, 5049305986, 4887817822, 4732848716, 4584062677, 4441145442, 4303802731, 4171758682, 4044754430, 3922546821, 3804907248, 3691620587, 3582484234, 3477307217, 3375909390, 3278120693, 3183780470, 3092736848, 3004846156, 2919972397, 2837986762, 2758767169, 2682197852, 2608168967, 2536576235, 2467320605, 2400307946, 2335448753, 2272657883, 2211854301, 2152960843, 2095904002, 2040613720, 1987023199, 1935068720, 1884689476, 1835827415, 1788427092, 1742435532, 1697802098, 1654478371, 1612418034, 1571576765, 1531912134, 1493383509, 1455951966, 1419580200, 1384232452, 1349874427, 1316473225, 1283997276, 1252416272, 1221701110, 1191823834, 1162757582, 1134476533, 1106955862, 1080171692, 1054101051, 1028721832, 1004012754, 979953324, 956523803, 933705173, 911479107, 889827934, 868734617, 848182721, 828156390, 808640322, 789619747, 771080402, 753008512, 735390770, 718214319, 701466729, 685135988, 669210476, 653678957, 638530562, 623754770, 609341400, 595280599, 581562821, 568178826, 555119661, 542376651, 529941391, 517805733, 505961779, 494401870, 483118578, 472104698, 461353240, 450857422, 440610661, 430606566, 420838935, 411301743, 401989141, 392895445, 384015137, 375342851, 366873376, 358601645, 350522735, 342631859, 334924360, 327395713, 320041514, 312857482, 305839449, 298983363, 292285278, 285741356, 279347860, 273101154, 266997696]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1005).prefactor = (1065518144122549/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1005).cutoff/(generalMeanRows 1005).c)).2 =
    (69093793820479/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1005).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1005).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1005).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1005

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1005).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1005).criticalRate j.val*(generalMeanRows 1005).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1005).c*(generalMeanRows 1005).criticalPoint j.val)).2-
      (generalMeanRows 1005).J/2-(generalMeanRows 1005).error (generalMeanGrid j.val)+
      (generalMeanRows 1005).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1005).c)).2-
      (generalMeanRows 1005).J/2-(generalMeanRows 1005).error 4 := by
  have he : (generalMeanRows 1005).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1005) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1005)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1005

/-! Kernel-checked entropy margins for general spectral rectangle 1006. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1006
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6041638962, 5843560846, 5653850864, 5472050752, 5297734180, 5130503950, 4969989507, 4815844707, 4667745817, 4525389717, 4388492282, 4256786917, 4130023228, 4007965824, 3890393214, 3777096815, 3667880036, 3562557447, 3460954014, 3362904396, 3268252302, 3176849894, 3088557244, 3003241824, 2920778044, 2841046814, 2763935146, 2689335784, 2617146856, 2547271555, 2479617838, 2414098152, 2350629174, 2289131564, 2229529747, 2171751696, 2115728740, 2061395373, 2008689088, 1957550210, 1907921745, 1859749240, 1812980647, 1767566197, 1723458282, 1680611344, 1638981773, 1598527803, 1559209424, 1520988292, 1483827648, 1447692238, 1412548243, 1378363206, 1345105969, 1312746611, 1281256388, 1250607678, 1220773931, 1191729615, 1163450174, 1135911979, 1109092291, 1082969215, 1057521668, 1032729339, 1008572657, 985032756, 962091450, 939731196, 917935074, 896686755, 875970480, 855771030, 836073713, 816864334, 798129177, 779854988, 762028954, 744638683, 727672192, 711117890, 694964558, 679201340, 663817725, 648803537, 634148919, 619844322, 605880497, 592248476, 578939569, 565945350, 553257649, 540868541, 528770338, 516955581, 505417030, 494147660, 483140649, 472389374, 461887402, 451628486, 441606557, 431815716, 422250233, 412904537, 403773214, 394850998, 386132772, 377613556, 369288508, 361152917, 353202200, 345431897, 337837668, 330415288, 323160645, 316069736, 309138663, 302363629, 295740938]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1006).prefactor = (1374404734488229/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1006).cutoff/(generalMeanRows 1006).c)).2 =
    (87915234837579/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1006).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1006).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1006).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1006

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1006).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1006).criticalRate j.val*(generalMeanRows 1006).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1006).c*(generalMeanRows 1006).criticalPoint j.val)).2-
      (generalMeanRows 1006).J/2-(generalMeanRows 1006).error (generalMeanGrid j.val)+
      (generalMeanRows 1006).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1006).c)).2-
      (generalMeanRows 1006).J/2-(generalMeanRows 1006).error 4 := by
  have he : (generalMeanRows 1006).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1006) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1006)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1006

/-! Kernel-checked entropy margins for general spectral rectangle 1007. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1007
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6518435782, 6315340874, 6120685225, 5934005536, 5754870942, 5582880170, 5417658994, 5258857974, 5106150411, 4959230527, 4817811812, 4681625531, 4550419381, 4423956263, 4302013165, 4184380152, 4070859436, 3961264527, 3855419456, 3753158065, 3654323345, 3558766841, 3466348087, 3376934098, 3290398892, 3206623054, 3125493328, 3046902235, 2970747732, 2896932877, 2825365533, 2755958080, 2688627158, 2623293419, 2559881296, 2498318794, 2438537286, 2380471330, 2324058488, 2269239169, 2215956470, 2164156035, 2113785916, 2064796449, 2017140136, 1970771527, 1925647118, 1881725255, 1838966031, 1797331206, 1756784123, 1717289625, 1678813984, 1641324832, 1604791094, 1569182925, 1534471653, 1500629722, 1467630640, 1435448928, 1404060075, 1373440491, 1343567469, 1314419140, 1285974438, 1258213062, 1231115445, 1204662720, 1178836687, 1153619790, 1128995082, 1104946204, 1081457357, 1058513282, 1036099234, 1014200959, 992804680, 971897071, 951465244, 931496726, 911979448, 892901722, 874252233, 856020020, 838194464, 820765274, 803722475, 787056395, 770757655, 754817156, 739226070, 723975833, 709058127, 694464881, 680188254, 666220631, 652554615, 639183017, 626098852, 613295327, 600765841, 588503973, 576503477, 564758278, 553262465, 542010286, 530996141, 520214581, 509660299, 499328127, 489213032, 479310112, 469614590, 460121812, 450827244, 441726463, 432815162, 424089139, 415544297, 407176642, 398982278]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1007).prefactor = (139616431180649/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1007).cutoff/(generalMeanRows 1007).c)).2 =
    (37681949898647/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1007).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1007).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1007).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1007

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1007).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1007).criticalRate j.val*(generalMeanRows 1007).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1007).c*(generalMeanRows 1007).criticalPoint j.val)).2-
      (generalMeanRows 1007).J/2-(generalMeanRows 1007).error (generalMeanGrid j.val)+
      (generalMeanRows 1007).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1007).c)).2-
      (generalMeanRows 1007).J/2-(generalMeanRows 1007).error 4 := by
  have he : (generalMeanRows 1007).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1007) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1007)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1007

/-! Kernel-checked entropy margins for general spectral rectangle 1008. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1008
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7432281980, 7224949421, 7025531600, 6833620465, 6648835952, 6470823470, 6299251672, 6133810470, 5974209269, 5820175379, 5671452598, 5527799926, 5388990417, 5254810131, 5125057185, 4999540899, 4878081003, 4760506930, 4646657158, 4536378609, 4429526105, 4325961854, 4225554994, 4128181155, 4033722068, 3942065195, 3853103393, 3766734594, 3682861515, 3601391385, 3522235694, 3445309952, 3370533472, 3297829167, 3227123348, 3158345556, 3091428383, 3026307321, 2962920610, 2901209097, 2841116112, 2782587337, 2725570693, 2670016233, 2615876034, 2563104105, 2511656293, 2461490194, 2412565076, 2364841799, 2318282740, 2272851726, 2228513970, 2185236003, 2142985622, 2101731829, 2061444779, 2022095731, 1983656999, 1946101907, 1909404745, 1873540728, 1838485958, 1804217386, 1770712775, 1737950669, 1705910358, 1674571852, 1643915846, 1613923695, 1584577386, 1555859518, 1527753268, 1500242378, 1473311126, 1446944308, 1421127216, 1395845622, 1371085754, 1346834286, 1323078313, 1299805341, 1277003270, 1254660376, 1232765302, 1211307041, 1190274923, 1169658605, 1149448058, 1129633553, 1110205654, 1091155207, 1072473325, 1054151386, 1036181018, 1018554092, 1001262713, 984299215, 967656147, 951326270, 935302550, 919578149, 904146418, 889000892, 874135284, 859543479, 845219526, 831157636, 817352173, 803797653, 790488737, 777420225, 764587053, 751984289, 739607129, 727450890, 715511012, 703783046, 692262658, 680945623, 669827820]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1008).prefactor = (1002043591626283/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1008).cutoff/(generalMeanRows 1008).c)).2 =
    (78233604032619/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1008).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1008).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1008).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1008

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1008).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1008).criticalRate j.val*(generalMeanRows 1008).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1008).c*(generalMeanRows 1008).criticalPoint j.val)).2-
      (generalMeanRows 1008).J/2-(generalMeanRows 1008).error (generalMeanGrid j.val)+
      (generalMeanRows 1008).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1008).c)).2-
      (generalMeanRows 1008).J/2-(generalMeanRows 1008).error 4 := by
  have he : (generalMeanRows 1008).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1008) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1008)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1008

/-! Kernel-checked entropy margins for general spectral rectangle 1009. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1009
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7171948488, 6968466646, 6772834218, 6584644217, 6403517575, 6229100644, 6061062974, 5899095351, 5742908025, 5592229142, 5446803319, 5306390377, 5170764183, 5039711609, 4913031588, 4790534254, 4672040158, 4557379553, 4446391739, 4338924467, 4234833383, 4133981527, 4036238866, 3941481860, 3849593070, 3760460786, 3673978690, 3590045538, 3508564867, 3429444719, 3352597396, 3277939210, 3205390275, 3134874290, 3066318353, 2999652778, 2934810924, 2871729039, 2810346112, 2750603728, 2692445944, 2635819157, 2580671997, 2526955209, 2474621557, 2423625720, 2373924205, 2325475259, 2278238786, 2232176269, 2187250700, 2143426506, 2100669489, 2058946758, 2018226672, 1978478789, 1939673802, 1901783502, 1864780719, 1828639282, 1793333976, 1758840499, 1725135424, 1692196162, 1660000926, 1628528699, 1597759198, 1567672851, 1538250758, 1509474672, 1481326969, 1453790621, 1426849175, 1400486730, 1374687912, 1349437858, 1324722189, 1300526999, 1276838831, 1253644661, 1230931884, 1208688294, 1186902071, 1165561766, 1144656287, 1124174886, 1104107146, 1084442968, 1065172560, 1046286427, 1027775358, 1009630417, 991842932, 974404486, 957306910, 940542271, 924102865, 907981210, 892170037, 876662282, 861451081, 846529762, 831891837, 817530999, 803441114, 789616214, 776050493, 762738303, 749674145, 736852669, 724268663, 711917056, 699792905, 687891399, 676207849, 664737688, 653476463, 642419835, 631563576, 620903561, 610435769]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1009).prefactor = (2493056194342993/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1009).cutoff/(generalMeanRows 1009).c)).2 =
    (12698461493417/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1009).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1009).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1009).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1009

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1009).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1009).criticalRate j.val*(generalMeanRows 1009).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1009).c*(generalMeanRows 1009).criticalPoint j.val)).2-
      (generalMeanRows 1009).J/2-(generalMeanRows 1009).error (generalMeanGrid j.val)+
      (generalMeanRows 1009).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1009).c)).2-
      (generalMeanRows 1009).J/2-(generalMeanRows 1009).error 4 := by
  have he : (generalMeanRows 1009).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1009) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1009)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1009

/-! Kernel-checked entropy margins for general spectral rectangle 1010. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1010
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6965171118, 6765911617, 6574406924, 6390252176, 6213070315, 6042509608, 5878241450, 5719958402, 5567372441, 5420213389, 5278227506, 5141176219, 5008834971, 4880992189, 4757448333, 4638015046, 4522514366, 4410778014, 4302646743, 4197969735, 4096604056, 3998414143, 3903271345, 3811053489, 3721644482, 3634933946, 3550816873, 3469193316, 3389968085, 3313050482, 3238354046, 3165796309, 3095298584, 3026785751, 2960186067, 2895430988, 2832454992, 2771195428, 2711592362, 2653588440, 2597128756, 2542160727, 2488633979, 2436500235, 2385713214, 2336228534, 2288003616, 2240997603, 2195171276, 2150486974, 2106908526, 2064401178, 2022931527, 1982467463, 1942978107, 1904433755, 1866805829, 1830066821, 1794190253, 1759150622, 1724923369, 1691484827, 1658812190, 1626883473, 1595677478, 1565173758, 1535352590, 1506194941, 1477682441, 1449797355, 1422522558, 1395841507, 1369738221, 1344197256, 1319203686, 1294743077, 1270801474, 1247365379, 1224421731, 1201957892, 1179961632, 1158421106, 1137324850, 1116661755, 1096421064, 1076592350, 1057165509, 1038130747, 1019478568, 1001199761, 983285393, 965726798, 948515565, 931643532, 915102773, 898885595, 882984526, 867392307, 852101887, 837106413, 822399225, 807973849, 793823992, 779943530, 766326512, 752967144, 739859792, 726998971, 714379343, 701995712, 689843018, 677916334, 666210859, 654721920, 643444961, 632375542, 621509337, 610842129, 600369805, 590088357, 579993873]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1010).prefactor = (495185347257101/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1010).cutoff/(generalMeanRows 1010).c)).2 =
    (81694209022561/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1010).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1010).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1010).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1010

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1010).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1010).criticalRate j.val*(generalMeanRows 1010).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1010).c*(generalMeanRows 1010).criticalPoint j.val)).2-
      (generalMeanRows 1010).J/2-(generalMeanRows 1010).error (generalMeanGrid j.val)+
      (generalMeanRows 1010).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1010).c)).2-
      (generalMeanRows 1010).J/2-(generalMeanRows 1010).error 4 := by
  have he : (generalMeanRows 1010).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1010) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1010)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1010

/-! Kernel-checked entropy margins for general spectral rectangle 1011. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1011
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6657735518, 6463286615, 6276493822, 6096954928, 5924295370, 5758165774, 5598239780, 5444212092, 5295796744, 5152725540, 5014746654, 4881623367, 4753132924, 4629065503, 4509223274, 4393419547, 4281477988, 4173231912, 4068523633, 3967203859, 3869131151, 3774171414, 3682197432, 3593088442, 3506729731, 3423012274, 3341832390, 3263091429, 3186695477, 3112555084, 3040585006, 2970703974, 2902834471, 2836902523, 2772837507, 2710571973, 2650041473, 2591184403, 2533941851, 2478257464, 2424077312, 2371349764, 2320025377, 2270056782, 2221398584, 2174007261, 2127841081, 2082860004, 2039025612, 1996301024, 1954650827, 1914041004, 1874438875, 1835813029, 1798133267, 1761370551, 1725496947, 1690485574, 1656310564, 1622947010, 1590370927, 1558559210, 1527489599, 1497140637, 1467491642, 1438522666, 1410214473, 1382548502, 1355506840, 1329072198, 1303227883, 1277957772, 1253246291, 1229078393, 1205439535, 1182315657, 1159693167, 1137558916, 1115900186, 1094704672, 1073960462, 1053656028, 1033780205, 1014322182, 995271486, 976617968, 958351795, 940463433, 922943641, 905783456, 888974184, 872507392, 856374897, 840568755, 825081255, 809904913, 795032457, 780456827, 766171160, 752168792, 738443242, 724988214, 711797582, 698865394, 686185857, 673753338, 661562355, 649607573, 637883801, 626385985, 615109204, 604048665, 593199702, 582557768, 572118434, 561877382, 551830407, 541973408, 532302387, 522813448, 513502788]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1011).prefactor = (4908606852629231/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1011).cutoff/(generalMeanRows 1011).c)).2 =
    (82541921014613/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1011).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1011).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1011).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1011

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1011).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1011).criticalRate j.val*(generalMeanRows 1011).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1011).c*(generalMeanRows 1011).criticalPoint j.val)).2-
      (generalMeanRows 1011).J/2-(generalMeanRows 1011).error (generalMeanGrid j.val)+
      (generalMeanRows 1011).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1011).c)).2-
      (generalMeanRows 1011).J/2-(generalMeanRows 1011).error 4 := by
  have he : (generalMeanRows 1011).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1011) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1011)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1011

/-! Kernel-checked entropy margins for general spectral rectangle 1012. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1012
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6456527597, 6266986464, 6084969143, 5910077201, 5741939668, 5580210603, 5424566933, 5274706529, 5130346474, 4991221525, 4857082713, 4727696094, 4602841614, 4482312076, 4365912209, 4253457819, 4144775009, 4039699474, 3938075848, 3839757115, 3744604052, 3652484736, 3563274073, 3476853371, 3393109948, 3311936759, 3233232061, 3156899097, 3082845804, 3010984537, 2941231821, 2873508109, 2807737567, 2743847864, 2681769982, 2621438034, 2562789098, 2505763057, 2450302451, 2396352341, 2343860173, 2292775660, 2243050665, 2194639093, 2147496787, 2101581433, 2056852470, 2013271002, 1970799720, 1929402822, 1889045946, 1849696097, 1811321584, 1773891959, 1737377962, 1701751462, 1666985406, 1633053773, 1599931526, 1567594564, 1536019687, 1505184550, 1475067629, 1445648183, 1416906223, 1388822476, 1361378355, 1334555931, 1308337906, 1282707583, 1257648844, 1233146124, 1209184389, 1185749115, 1162826265, 1140402270, 1118464013, 1096998805, 1075994375, 1055438846, 1035320726, 1015628889, 996352563, 977481315, 959005037, 940913935, 923198519, 905849588, 888858221, 872215765, 855913828, 839944267, 824299180, 808970895, 793951966, 779235160, 764813455, 750680027, 736828245, 723251666, 709944026, 696899237, 684111376, 671574684, 659283559, 647232549, 635416349, 623829796, 612467863, 601325657, 590398411, 579681483, 569170351, 558860608, 548747961, 538828225, 529097320, 519551270, 510186195, 500998314, 491983938]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1012).prefactor = (607181431029591/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1012).cutoff/(generalMeanRows 1012).c)).2 =
    (170911882290033/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1012).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1012).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1012).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1012

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1012).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1012).criticalRate j.val*(generalMeanRows 1012).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1012).c*(generalMeanRows 1012).criticalPoint j.val)).2-
      (generalMeanRows 1012).J/2-(generalMeanRows 1012).error (generalMeanGrid j.val)+
      (generalMeanRows 1012).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1012).c)).2-
      (generalMeanRows 1012).J/2-(generalMeanRows 1012).error 4 := by
  have he : (generalMeanRows 1012).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1012) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1012)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1012

/-! Kernel-checked entropy margins for general spectral rectangle 1013. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1013
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5975493530, 5781134305, 5594727562, 5415854497, 5244124918, 5079174719, 4920663638, 4768273255, 4621705199, 4480679546, 4344933373, 4214219450, 4088305065, 3966970955, 3850010334, 3737228007, 3628439568, 3523470659, 3422156297, 3324340253, 3229874483, 3138618605, 3050439416, 2965210445, 2882811539, 2803128488, 2726052661, 2651480687, 2579314144, 2509459277, 2441826732, 2376331312, 2312891745, 2251430470, 2191873434, 2134149905, 2078192299, 2023936007, 1971319248, 1920282920, 1870770461, 1822727725, 1776102858, 1730846184, 1686910100, 1644248970, 1602819036, 1562578323, 1523486556, 1485505078, 1448596775, 1412726006, 1377858530, 1343961446, 1311003131, 1278953182, 1247782358, 1217462533, 1187966645, 1159268647, 1131343464, 1104166952, 1077715855, 1051967771, 1026901110, 1002495065, 978729575, 955585296, 933043572, 911086402, 889696419, 868856861, 848551545, 828764846, 809481675, 790687457, 772368107, 754510017, 737100032, 720125437, 703573935, 687433635, 671693033, 656341000, 641366767, 626759910, 612510341, 598608289, 585044295, 571809196, 558894117, 546290456, 533989881, 521984315, 510265927, 498827127, 487660554, 476759068, 466115745, 455723867, 445576914, 435668561, 425992667, 416543272, 407314590, 398301002, 389497049, 380897433, 372497004, 364290758, 356273837, 348441515, 340789200, 333312431, 326006867, 318868290, 311892596, 305075795, 298414007, 291903455, 285540466]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1013).prefactor = (1265148067922739/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1013).cutoff/(generalMeanRows 1013).c)).2 =
    (288299284164359/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1013).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1013).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1013).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1013

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1013).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1013).criticalRate j.val*(generalMeanRows 1013).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1013).c*(generalMeanRows 1013).criticalPoint j.val)).2-
      (generalMeanRows 1013).J/2-(generalMeanRows 1013).error (generalMeanGrid j.val)+
      (generalMeanRows 1013).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1013).c)).2-
      (generalMeanRows 1013).J/2-(generalMeanRows 1013).error 4 := by
  have he : (generalMeanRows 1013).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1013) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1013)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1013

/-! Kernel-checked entropy margins for general spectral rectangle 1014. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1014
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5861841795, 5672755403, 5491435061, 5317468221, 5150470641, 4990083897, 4835973166, 4687825246, 4545346783, 4408262687, 4276314693, 4149260074, 4026870475, 3908930845, 3795238481, 3685602151, 3579841288, 3477785262, 3379272712, 3284150924, 3192275272, 3103508696, 3017721218, 2934789507, 2854596459, 2777030829, 2701986870, 2629364012, 2559066558, 2491003400, 2425087759, 2361236939, 2299372097, 2239418034, 2181302990, 2124958463, 2070319030, 2017322185, 1965908187, 1916019911, 1867602720, 1820604329, 1774974695, 1730665896, 1687632028, 1645829109, 1605214977, 1565749209, 1527393031, 1490109242, 1453862138, 1418617443, 1384342239, 1351004907, 1318575061, 1287023498, 1256322139, 1226443981, 1197363047, 1169054341, 1141493805, 1114658277, 1088525450, 1063073839, 1038282742, 1014132207, 990603003, 967676583, 945335063, 923561188, 902338309, 881650357, 861481821, 841817722, 822643593, 803945458, 785709815, 767923614, 750574238, 733649490, 717137574, 701027080, 685306969, 669966559, 654995510, 640383814, 626121779, 612200019, 598609444, 585341247, 572386891, 559738106, 547386874, 535325421, 523546207, 512041924, 500805477, 489829986, 479108774, 468635361, 458403455, 448406951, 438639918, 429096597, 419771395, 410658876, 401753762, 393050921, 384545368, 376232254, 368106869, 360164631, 352401083, 344811894, 337392848, 330139844, 323048894, 316116116, 309337731, 302710063, 296229532]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1014).prefactor = (1247049331142919/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1014).cutoff/(generalMeanRows 1014).c)).2 =
    (154213848711023/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1014).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1014).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1014).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1014

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1014).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1014).criticalRate j.val*(generalMeanRows 1014).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1014).c*(generalMeanRows 1014).criticalPoint j.val)).2-
      (generalMeanRows 1014).J/2-(generalMeanRows 1014).error (generalMeanGrid j.val)+
      (generalMeanRows 1014).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1014).c)).2-
      (generalMeanRows 1014).J/2-(generalMeanRows 1014).error 4 := by
  have he : (generalMeanRows 1014).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1014) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1014)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1014

/-! Kernel-checked entropy margins for general spectral rectangle 1015. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1015
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5838160963, 5654101422, 5477594338, 5308234541, 5145644844, 4989473588, 4839392443, 4695094459, 4556292306, 4422716707, 4294115017, 4170249943, 4050898388, 3935850400, 3824908216, 3717885392, 3614606011, 3514903956, 3418622241, 3325612406, 3235733954, 3148853834, 3064845962, 2983590789, 2904974884, 2828890569, 2755235559, 2683912649, 2614829406, 2547897891, 2483034401, 2420159224, 2359196416, 2300073586, 2242721700, 2187074898, 2133070320, 2080647945, 2029750436, 1980323005, 1932313271, 1885671141, 1840348690, 1796300048, 1753481300, 1711850383, 1671366998, 1631992518, 1593689912, 1556423660, 1520159685, 1484865283, 1450509056, 1417060849, 1384491696, 1352773762, 1321880287, 1291785545, 1262464789, 1233894210, 1206050894, 1178912782, 1152458632, 1126667985, 1101521126, 1076999056, 1053083459, 1029756671, 1007001658, 984801983, 963141782, 942005744, 921379084, 901247522, 881597263, 862414978, 843687783, 825403223, 807549253, 790114224, 773086866, 756456272, 740211886, 724343489, 708841185, 693695391, 678896819, 664436475, 650305638, 636495856, 622998933, 609806922, 596912115, 584307032, 571984417, 559937226, 548158622, 536641968, 525380818, 514368911, 503600165, 493068672, 482768688, 472694634, 462841084, 453202763, 443774542, 434551432, 425528582, 416701270, 408064904, 399615012, 391347245, 383257367, 375341254, 367594892, 360014371, 352595882, 345335716, 338230259, 331275989]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1015).prefactor = (306925679684923/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1015).cutoff/(generalMeanRows 1015).c)).2 =
    (83994685347189/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1015).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1015).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1015).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1015

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1015).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1015).criticalRate j.val*(generalMeanRows 1015).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1015).c*(generalMeanRows 1015).criticalPoint j.val)).2-
      (generalMeanRows 1015).J/2-(generalMeanRows 1015).error (generalMeanGrid j.val)+
      (generalMeanRows 1015).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1015).c)).2-
      (generalMeanRows 1015).J/2-(generalMeanRows 1015).error 4 := by
  have he : (generalMeanRows 1015).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1015) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1015)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1015

/-! Kernel-checked entropy margins for general spectral rectangle 1016. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1016
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5732874279, 5554435239, 5383335457, 5219177232, 5061590508, 4910230450, 4764775275, 4624924317, 4490396299, 4360927773, 4236271717, 4116196267, 4000483577, 3888928766, 3781338985, 3677532543, 3577338129, 3480594086, 3387147754, 3296854862, 3209578977, 3125190986, 3043568626, 2964596048, 2888163414, 2814166525, 2742506474, 2673089325, 2605825817, 2540631086, 2477424407, 2416128956, 2356671585, 2298982612, 2242995628, 2188647314, 2135877270, 2084627858, 2034844049, 1986473283, 1939465341, 1893772218, 1849348009, 1806148799, 1764132563, 1723259065, 1683489770, 1644787761, 1607117652, 1570445518, 1534738821, 1499966343, 1466098119, 1433105382, 1400960501, 1369636932, 1339109162, 1309352664, 1280343850, 1252060030, 1224479366, 1197580838, 1171344208, 1145749979, 1120779368, 1096414271, 1072637235, 1049431430, 1026780619, 1004669138, 983081865, 962004202, 941422052, 921321797, 901690278, 882514776, 863782998, 845483053, 827603440, 810133034, 793061065, 776377111, 760071080, 744133196, 728553993, 713324295, 698435213, 683878127, 669644680, 655726769, 642116532, 628806341, 615788795, 603056709, 590603108, 578421219, 566504463, 554846451, 543440974, 532281997, 521363656, 510680251, 500226236, 489996222, 479984963, 470187360, 460598448, 451213397, 442027505, 433036195, 424235012, 415619615, 407185780, 398929388, 390846431, 382933000, 375185289, 367599585, 360172272, 352899824, 345778801]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1016).prefactor = (2414593085524973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1016).cutoff/(generalMeanRows 1016).c)).2 =
    (358127365974317/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1016).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1016).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1016).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1016

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1016).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1016).criticalRate j.val*(generalMeanRows 1016).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1016).c*(generalMeanRows 1016).criticalPoint j.val)).2-
      (generalMeanRows 1016).J/2-(generalMeanRows 1016).error (generalMeanGrid j.val)+
      (generalMeanRows 1016).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1016).c)).2-
      (generalMeanRows 1016).J/2-(generalMeanRows 1016).error 4 := by
  have he : (generalMeanRows 1016).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1016) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1016)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1016

/-! Kernel-checked entropy margins for general spectral rectangle 1017. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1017
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5349948241, 5168558393, 4994854671, 4828421681, 4668872674, 4515847043, 4369008084, 4228041002, 4092651123, 3962562285, 3837515387, 3717267086, 3601588605, 3490264662, 3383092493, 3279880956, 3180449718, 3084628515, 2992256463, 2903181436, 2817259489, 2734354327, 2654336816, 2577084530, 2502481340, 2430417016, 2360786879, 2293491465, 2228436212, 2165531179, 2104690775, 2045833510, 1988881761, 1933761561, 1880402386, 1828736977, 1778701152, 1730233647, 1683275956, 1637772187, 1593668922, 1550915094, 1509461858, 1469262482, 1430272241, 1392448311, 1355749678, 1320137048, 1285572759, 1252020707, 1219446266, 1187816218, 1157098687, 1127263074, 1098280000, 1070121244, 1042759692, 1016169290, 990324987, 965202697, 940779252, 917032361, 893940572, 871483236, 849640469, 828393118, 807722736, 787611543, 768042404, 748998797, 730464791, 712425019, 694864655, 677769392, 661125420, 644919406, 629138476, 613770192, 598802543, 584223918, 570023096, 556189233, 542711839, 529580773, 516786224, 504318700, 492169017, 480328284, 468787898, 457539526, 446575101, 435886807, 425467075, 415308570, 405404184, 395747028, 386330424, 377147897, 368193170, 359460152, 350942937, 342635794, 334533165, 326629653, 318920021, 311399186, 304062212, 296904308, 289920819, 283107226, 276459139, 269972291, 263642540, 257465857, 251438329, 245556153, 239815629, 234213164, 228745263, 223408525, 218199646]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1017).prefactor = (4997995123910217/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1017).cutoff/(generalMeanRows 1017).c)).2 =
    (314506743498429/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1017).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1017).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1017).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1017

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1017).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1017).criticalRate j.val*(generalMeanRows 1017).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1017).c*(generalMeanRows 1017).criticalPoint j.val)).2-
      (generalMeanRows 1017).J/2-(generalMeanRows 1017).error (generalMeanGrid j.val)+
      (generalMeanRows 1017).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1017).c)).2-
      (generalMeanRows 1017).J/2-(generalMeanRows 1017).error 4 := by
  have he : (generalMeanRows 1017).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1017) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1017)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1017

/-! Kernel-checked entropy margins for general spectral rectangle 1018. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1018
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5481139240, 5304252030, 5134770921, 4972291447, 4816437337, 4666858036, 4523226508, 4385237261, 4252604581, 4125060945, 4002355592, 3884253223, 3770532839, 3660986667, 3555419202, 3453646323, 3355494486, 3260799988, 3169408296, 3081173426, 2995957370, 2913629579, 2834066475, 2757151007, 2682772238, 2610824965, 2541209364, 2473830663, 2408598838, 2345428331, 2284237782, 2224949793, 2167490689, 2111790313, 2057781824, 2005401510, 1954588616, 1905285180, 1857435883, 1810987902, 1765890780, 1722096300, 1679558364, 1638232885, 1598077682, 1559052383, 1521118331, 1484238498, 1448377403, 1413501037, 1379576787, 1346573370, 1314460767, 1283210162, 1252793885, 1223185357, 1194359039, 1166290383, 1138955784, 1112332541, 1086398809, 1061133567, 1036516576, 1012528345, 989150098, 966363743, 944151841, 922497578, 901384736, 880797673, 860721290, 841141017, 822042782, 803412997, 785238536, 767506714, 750205270, 733322352, 716846497, 700766618, 685071988, 669752227, 654797285, 640197433, 625943251, 612025612, 598435674, 585164868, 572204890, 559547687, 547185453, 535110614, 523315824, 511793957, 500538096, 489541525, 478797729, 468300376, 458043322, 448020595, 438226396, 428655087, 419301191, 410159384, 401224491, 392491477, 383955450, 375611649, 367455443, 359482327, 351687918, 344067949, 336618269, 329334835, 322213713, 315251071, 308443178, 301786399, 295277195, 288912118, 282687808]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1018).prefactor = (4900586141633259/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1018).cutoff/(generalMeanRows 1018).c)).2 =
    (178242496187913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1018).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1018).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1018).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1018

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1018).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1018).criticalRate j.val*(generalMeanRows 1018).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1018).c*(generalMeanRows 1018).criticalPoint j.val)).2-
      (generalMeanRows 1018).J/2-(generalMeanRows 1018).error (generalMeanGrid j.val)+
      (generalMeanRows 1018).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1018).c)).2-
      (generalMeanRows 1018).J/2-(generalMeanRows 1018).error 4 := by
  have he : (generalMeanRows 1018).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1018) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1018)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1018

/-! Kernel-checked entropy margins for general spectral rectangle 1019. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1019
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5496554674, 5314787579, 5140697288, 4973864862, 4813900494, 4660440959, 4513147338, 4371702983, 4235811695, 4105196083, 3979596087, 3858767645, 3742481480, 3630522004, 3522686322, 3418783314, 3318632815, 3222064845, 3128918918, 3039043398, 2952294916, 2868537826, 2787643705, 2709490895, 2633964074, 2560953866, 2490356471, 2422073328, 2356010803, 2292079894, 2230195958, 2170278460, 2112250734, 2056039765, 2001575983, 1948793069, 1897627775, 1848019758, 1799911419, 1753247759, 1707976237, 1664046642, 1621410967, 1580023302, 1539839716, 1500818164, 1462918388, 1426101825, 1390331525, 1355572070, 1321789501, 1288951242, 1257026036, 1225983883, 1195795976, 1166434648, 1137873316, 1110086432, 1083049435, 1056738704, 1031131516, 1006206005, 981941125, 958316611, 935312946, 912911327, 891093634, 869842400, 849140785, 828972545, 809322011, 790174061, 771514101, 753328039, 735602266, 718323637, 701479451, 685057434, 669045719, 653432834, 638207683, 623359533, 608877998, 594753029, 580974895, 567534178, 554421756, 541628793, 529146730, 516967273, 505082383, 493484267, 482165369, 471118364, 460336144, 449811816, 439538690, 429510275, 419720271, 410162562, 400831208, 391720443, 382824666, 374138436, 365656467, 357373622, 349284910, 341385479, 333670611, 326135723, 318776354, 311588168, 304566948, 297708590, 291009103, 284464603, 278071311, 271825548, 265723733, 259762383, 253938104]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1019).prefactor = (2531161559287533/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1019).cutoff/(generalMeanRows 1019).c)).2 =
    (344252423940191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1019).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1019).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1019).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1019

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1019).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1019).criticalRate j.val*(generalMeanRows 1019).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1019).c*(generalMeanRows 1019).criticalPoint j.val)).2-
      (generalMeanRows 1019).J/2-(generalMeanRows 1019).error (generalMeanGrid j.val)+
      (generalMeanRows 1019).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1019).c)).2-
      (generalMeanRows 1019).J/2-(generalMeanRows 1019).error 4 := by
  have he : (generalMeanRows 1019).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1019) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1019)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1019

/-! Kernel-checked entropy margins for general spectral rectangle 1020. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1020
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5677960757, 5490194694, 5310358797, 5138020300, 4972776532, 4814252281, 4662097440, 4515984913, 4375608723, 4240682326, 4110937078, 3986120863, 3865996836, 3750342295, 3638947646, 3531615466, 3428159640, 3328404579, 3232184501, 3139342765, 3049731272, 2963209896, 2879645978, 2798913844, 2720894367, 2645474559, 2572547195, 2502010463, 2433767638, 2367726779, 2303800450, 2241905459, 2181962609, 2123896476, 2067635193, 2013110253, 1960256320, 1909011059, 1859314973, 1811111244, 1764345599, 1718966169, 1674923364, 1632169756, 1590659968, 1550350564, 1511199959, 1473168317, 1436217468, 1400310826, 1365413311, 1331491271, 1298512419, 1266445763, 1235261546, 1204931189, 1175427230, 1146723279, 1118793964, 1091614884, 1065162566, 1039414424, 1014348716, 989944508, 966181639, 943040686, 920502930, 898550330, 877165486, 856331622, 836032549, 816252648, 796976842, 778190575, 759879788, 742030902, 724630798, 707666795, 691126636, 674998469, 659270834, 643932641, 628973163, 614382019, 600149157, 586264848, 572719669, 559504492, 546610477, 534029054, 521751919, 509771023, 498078562, 486666965, 475528893, 464657224, 454045048, 443685660, 433572551, 423699402, 414060080, 404648627, 395459258, 386486351, 377724446, 369168237, 360812569, 352652428, 344682942, 336899375, 329297121, 321871699, 314618753, 307534045, 300613451, 293852959, 287248665, 280796769, 274493573, 268335477, 262318975]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1020).prefactor = (2614698998875119/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1020).cutoff/(generalMeanRows 1020).c)).2 =
    (344252423940191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1020).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1020).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1020).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1020

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1020).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1020).criticalRate j.val*(generalMeanRows 1020).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1020).c*(generalMeanRows 1020).criticalPoint j.val)).2-
      (generalMeanRows 1020).J/2-(generalMeanRows 1020).error (generalMeanGrid j.val)+
      (generalMeanRows 1020).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1020).c)).2-
      (generalMeanRows 1020).J/2-(generalMeanRows 1020).error 4 := by
  have he : (generalMeanRows 1020).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1020) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1020)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1020

/-! Kernel-checked entropy margins for general spectral rectangle 1021. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1021
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5865353893, 5671390875, 5485619746, 5307593459, 5136896052, 4973139930, 4815963432, 4665028665, 4520019556, 4380640102, 4246612795, 4117677195, 3993588643, 3874117086, 3759046013, 3648171484, 3541301244, 3438253907, 3338858220, 3242952373, 3150383378, 3061006485, 2974684658, 2891288073, 2810693672, 2732784739, 2657450510, 2584585812, 2514090728, 2445870282, 2379834155, 2315896406, 2253975226, 2193992702, 2135874595, 2079550135, 2024951832, 1972015294, 1920679057, 1870884432, 1822575353, 1775698238, 1730201862, 1686037231, 1643157470, 1601517712, 1561074996, 1521788172, 1483617812, 1446526123, 1410476863, 1375435274, 1341368001, 1308243030, 1276029622, 1244698254, 1214220558, 1184569274, 1155718191, 1127642103, 1100316764, 1073718840, 1047825873, 1022616239, 998069110, 974164422, 950882840, 928205724, 906115104, 884593647, 863624632, 843191923, 823279946, 803873664, 784958555, 766520592, 748546221, 731022345, 713936302, 697275848, 681029143, 665184735, 649731541, 634658836, 619956239, 605613697, 591621479, 577970154, 564650589, 551653934, 538971610, 526595301, 514516946, 502728726, 491223058, 479992584, 469030168, 458328883, 447882005, 437683007, 427725553, 418003488, 408510836, 399241791, 390190712, 381352118, 372720682, 364291227, 356058720, 348018267, 340165111, 332494623, 325002304, 317683775, 310534776, 303551164, 296728904, 290064073, 283552848, 277191513, 270976445]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1021).prefactor = (5401986949140397/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1021).cutoff/(generalMeanRows 1021).c)).2 =
    (344252423940191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1021).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1021).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1021).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1021

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1021).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1021).criticalRate j.val*(generalMeanRows 1021).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1021).c*(generalMeanRows 1021).criticalPoint j.val)).2-
      (generalMeanRows 1021).J/2-(generalMeanRows 1021).error (generalMeanGrid j.val)+
      (generalMeanRows 1021).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1021).c)).2-
      (generalMeanRows 1021).J/2-(generalMeanRows 1021).error 4 := by
  have he : (generalMeanRows 1021).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1021) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1021)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1021

/-! Kernel-checked entropy margins for general spectral rectangle 1022. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1022
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6149300345, 5948393699, 5755935120, 5571463434, 5394549575, 5224793771, 5061823031, 4905288908, 4754865484, 4610247563, 4471149047, 4337301453, 4208452591, 4084365347, 3964816582, 3849596134, 3738505895, 3631358976, 3527978942, 3428199099, 3331861854, 3238818116, 3148926742, 3062054034, 2978073270, 2896864263, 2818312969, 2742311102, 2668755798, 2597549285, 2528598588, 2461815247, 2397115059, 2334417832, 2273647161, 2214730215, 2157597541, 2102182874, 2048422968, 1996257430, 1945628570, 1896481255, 1848762776, 1802422723, 1757412864, 1713687032, 1671201025, 1629912503, 1589780894, 1550767308, 1512834456, 1475946567, 1440069316, 1405169759, 1371216257, 1338178426, 1306027068, 1274734119, 1244272600, 1214616560, 1185741034, 1157621997, 1130236321, 1103561735, 1077576788, 1052260810, 1027593880, 1003556794, 980131033, 957298733, 935042656, 913346168, 892193210, 871568274, 851456382, 831843061, 812714328, 794056665, 775857001, 758102697, 740781526, 723881658, 707391645, 691300403, 675597204, 660271656, 645313693, 630713565, 616461822, 602549304, 588967133, 575706699, 562759652, 550117893, 537773564, 525719041, 513946922, 502450024, 491221371, 480254191, 469541906, 459078125, 448856641, 438871420, 429116601, 419586484, 410275529, 401178351, 392289709, 383604512, 375117802, 366824759, 358720692, 350801037, 343061352, 335497313, 328104710, 320879445, 313817529, 306915076, 300168301]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1022).prefactor = (1395067989242617/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1022).cutoff/(generalMeanRows 1022).c)).2 =
    (35035000380831/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1022).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1022).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1022).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1022

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1022).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1022).criticalRate j.val*(generalMeanRows 1022).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1022).c*(generalMeanRows 1022).criticalPoint j.val)).2-
      (generalMeanRows 1022).J/2-(generalMeanRows 1022).error (generalMeanGrid j.val)+
      (generalMeanRows 1022).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1022).c)).2-
      (generalMeanRows 1022).J/2-(generalMeanRows 1022).error 4 := by
  have he : (generalMeanRows 1022).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1022) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1022)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1022

/-! Kernel-checked entropy margins for general spectral rectangle 1023. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1023
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6447331587, 6239263438, 6039906906, 5848786229, 5665458807, 5489512291, 5320561997, 5158248581, 5002235966, 4852209471, 4707874130, 4568953169, 4435186629, 4306330115, 4182153659, 4062440682, 3946987048, 3835600199, 3728098362, 3624309816, 3524072230, 3427232040, 3333643884, 3243170078, 3155680130, 3071050292, 2989163143, 2909907206, 2833176588, 2758870647, 2686893684, 2617154655, 2549566901, 2484047895, 2420519015, 2358905318, 2299135339, 2241140899, 2184856927, 2130221290, 2077174636, 2025660248, 1975623902, 1927013740, 1879780145, 1833875630, 1789254721, 1745873865, 1703691326, 1662667100, 1622762825, 1583941703, 1546168424, 1509409093, 1473631162, 1438803366, 1404895665, 1371879183, 1339726156, 1308409878, 1277904657, 1248185763, 1219229392, 1191012615, 1163513349, 1136710310, 1110582987, 1085111600, 1060277075, 1036061010, 1012445647, 989413844, 966949052, 945035287, 923657108, 902799594, 882448324, 862589355, 843209205, 824294833, 805833619, 787813354, 770222217, 753048765, 736281915, 719910932, 703925416, 688315289, 673070779, 658182418, 643641020, 629437679, 615563754, 602010860, 588770862, 575835862, 563198194, 550850412, 538785287, 526995796, 515475115, 504216616, 493213855, 482460569, 471950669, 461678237, 451637514, 441822902, 432228954, 422850371, 413681996, 404718811, 395955932, 387388605, 379012202, 370822214, 362814253, 354984045, 347327426, 339840340, 332518835]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1023).prefactor = (5764441011599659/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1023).cutoff/(generalMeanRows 1023).c)).2 =
    (178242496187913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1023).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1023).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1023).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1023

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1023).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1023).criticalRate j.val*(generalMeanRows 1023).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1023).c*(generalMeanRows 1023).criticalPoint j.val)).2-
      (generalMeanRows 1023).J/2-(generalMeanRows 1023).error (generalMeanGrid j.val)+
      (generalMeanRows 1023).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1023).c)).2-
      (generalMeanRows 1023).J/2-(generalMeanRows 1023).error 4 := by
  have he : (generalMeanRows 1023).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1023) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1023)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1023

/-! Kernel-checked entropy margins for general spectral rectangle 1024. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1024
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7200177256, 6989703488, 6787357616, 6592721246, 6405404588, 6225043903, 6051299223, 5883852334, 5722404970, 5566677194, 5416405950, 5271343754, 5131257518, 4995927476, 4865146222, 4738717829, 4616457043, 4498188556, 4383746336, 4272973010, 4165719305, 4061843529, 3961211093, 3863694074, 3769170805, 3677525502, 3588647916, 3502433007, 3418780646, 3337595338, 3258785957, 3182265509, 3107950902, 3035762739, 2965625118, 2897465446, 2831214270, 2766805111, 2704174316, 2643260910, 2584006464, 2526354971, 2470252722, 2415648200, 2362491967, 2310736572, 2260336450, 2211247840, 2163428694, 2116838604, 2071438720, 2027191688, 1984061574, 1942013803, 1901015102, 1861033437, 1822037963, 1783998970, 1746887835, 1710676972, 1675339795, 1640850666, 1607184864, 1574318541, 1542228688, 1510893099, 1480290340, 1450399716, 1421201239, 1392675606, 1364804165, 1337568890, 1310952361, 1284937735, 1259508724, 1234649577, 1210345055, 1186580414, 1163341385, 1140614155, 1118385354, 1096642031, 1075371645, 1054562046, 1034201463, 1014278488, 994782063, 975701468, 957026310, 938746506, 920852280, 903334144, 886182894, 869389595, 852945576, 836842417, 821071944, 805626216, 790497522, 775678369, 761161477, 746939770, 733006371, 719354595, 705977941, 692870087, 680024886, 667436357, 655098679, 643006192, 631153384, 619534892, 608145495, 596980107, 586033779, 575301689, 564779141, 554461558, 544344483, 534423572, 524694592]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1024).prefactor = (516911606153881/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1024).cutoff/(generalMeanRows 1024).c)).2 =
    (294192581600173/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1024).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1024).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1024).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1024

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1024).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1024).criticalRate j.val*(generalMeanRows 1024).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1024).c*(generalMeanRows 1024).criticalPoint j.val)).2-
      (generalMeanRows 1024).J/2-(generalMeanRows 1024).error (generalMeanGrid j.val)+
      (generalMeanRows 1024).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1024).c)).2-
      (generalMeanRows 1024).J/2-(generalMeanRows 1024).error 4 := by
  have he : (generalMeanRows 1024).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1024) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1024)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1024

/-! Kernel-checked entropy margins for general spectral rectangle 1025. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1025
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6960001344, 6754990104, 6557969092, 6368524039, 6186269032, 6010843990, 5841912413, 5679159387, 5522289798, 5371026730, 5225110029, 5084295007, 4948351274, 4817061680, 4690221349, 4567636812, 4449125205, 4334513545, 4223638064, 4116343598, 4012483028, 3911916765, 3814512272, 3720143634, 3628691144, 3540040936, 3454084633, 3370719030, 3289845790, 3211371168, 3135205756, 3061264233, 2989465149, 2919730709, 2851986577, 2786161695, 2722188107, 2660000799, 2599537546, 2540738774, 2483547420, 2427908809, 2373770539, 2321082362, 2269796085, 2219865469, 2171246133, 2123895471, 2077772563, 2032838100, 1989054305, 1946384869, 1904794878, 1864250753, 1824720188, 1786172094, 1748576547, 1711904733, 1676128902, 1641222321, 1607159228, 1573914797, 1541465089, 1509787021, 1478858329, 1448657532, 1419163899, 1390357420, 1362218778, 1334729316, 1307871013, 1281626458, 1255978828, 1230911860, 1206409831, 1182457539, 1159040277, 1136143821, 1113754405, 1091858707, 1070443831, 1049497291, 1029006993, 1008961226, 989348642, 970158244, 951379377, 933001708, 915015223, 897410205, 880177235, 863307171, 846791146, 830620550, 814787031, 799282475, 784099009, 769228982, 754664964, 740399736, 726426285, 712737793, 699327634, 686189367, 673316726, 660703621, 648344125, 636232476, 624363063, 612730430, 601329264, 590154395, 579200787, 568463540, 557937877, 547619151, 537502831, 527584503, 517859867, 508324732, 498975013]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1025).prefactor = (638490242709709/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1025).cutoff/(generalMeanRows 1025).c)).2 =
    (304849876074161/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1025).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1025).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1025).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1025

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1025).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1025).criticalRate j.val*(generalMeanRows 1025).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1025).c*(generalMeanRows 1025).criticalPoint j.val)).2-
      (generalMeanRows 1025).J/2-(generalMeanRows 1025).error (generalMeanGrid j.val)+
      (generalMeanRows 1025).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1025).c)).2-
      (generalMeanRows 1025).J/2-(generalMeanRows 1025).error 4 := by
  have he : (generalMeanRows 1025).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1025) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1025)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1025

/-! Kernel-checked entropy margins for general spectral rectangle 1026. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1026
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6827052053, 6627434806, 6435639757, 6251257774, 6073907813, 5903234429, 5738905549, 5580610501, 5428058243, 5280975784, 5139106757, 5002210136, 4870059078, 4742439870, 4619150978, 4500002180, 4384813772, 4273415847, 4165647634, 4061356893, 3960399355, 3862638210, 3767943639, 3676192373, 3587267294, 3501057059, 3417455759, 3336362596, 3257681584, 3181321276, 3107194504, 3035218137, 2965312861, 2897402967, 2831416154, 2767283351, 2704938540, 2644318597, 2585363144, 2528014401, 2472217062, 2417918162, 2365066963, 2313614843, 2263515191, 2214723308, 2167196317, 2120893073, 2075774079, 2031801412, 1988938645, 1947150781, 1906404183, 1866666514, 1827906678, 1790094759, 1753201976, 1717200626, 1682064038, 1647766526, 1614283351, 1581590673, 1549665517, 1518485733, 1488029962, 1458277605, 1429208784, 1400804320, 1373045699, 1345915043, 1319395091, 1293469165, 1268121154, 1243335484, 1219097104, 1195391459, 1172204472, 1149522527, 1127332449, 1105621488, 1084377302, 1063587940, 1043241830, 1023327762, 1003834876, 984752647, 966070873, 947779666, 929869436, 912330882, 895154981, 878332981, 861856386, 845716949, 829906666, 814417763, 799242689, 784374110, 769804903, 755528140, 741537094, 727825220, 714386158, 701213722, 688301894, 675644821, 663236807, 651072311, 639145937, 627452435, 615986690, 604743725, 593718690, 582906860, 572303635, 561904529, 551705172, 541701305, 531888774, 522263532, 512821629]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1026).prefactor = (315065567525113/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1026).cutoff/(generalMeanRows 1026).c)).2 =
    (161737312955933/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1026).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1026).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1026).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1026

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1026).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1026).criticalRate j.val*(generalMeanRows 1026).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1026).c*(generalMeanRows 1026).criticalPoint j.val)).2-
      (generalMeanRows 1026).J/2-(generalMeanRows 1026).error (generalMeanGrid j.val)+
      (generalMeanRows 1026).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1026).c)).2-
      (generalMeanRows 1026).J/2-(generalMeanRows 1026).error 4 := by
  have he : (generalMeanRows 1026).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1026) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1026)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1026

/-! Kernel-checked entropy margins for general spectral rectangle 1027. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1027
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6598247025, 6404471173, 6218351547, 6039484354, 5867493601, 5702028636, 5542761952, 5389387237, 5241617629, 5099184147, 4961834283, 4829330730, 4701450236, 4577982563, 4458729537, 4343504194, 4232129989, 4124440083, 4020276685, 3919490450, 3821939925, 3727491042, 3636016643, 3547396057, 3461514689, 3378263658, 3297539447, 3219243590, 3143282374, 3069566560, 2998011135, 2928535065, 2861061077, 2795515450, 2731827820, 2669930998, 2609760800, 2551255887, 2494357617, 2439009901, 2385159076, 2332753775, 2281744816, 2232085089, 2183729452, 2136634638, 2090759156, 2046063212, 2002508622, 1960058737, 1918678368, 1878333720, 1838992324, 1800622978, 1763195685, 1726681600, 1691052979, 1656283124, 1622346342, 1589217895, 1556873963, 1525291599, 1494448692, 1464323931, 1434896772, 1406147403, 1378056711, 1350606259, 1323778251, 1297555506, 1271921436, 1246860020, 1222355777, 1198393751, 1174959483, 1152038993, 1129618765, 1107685722, 1086227213, 1065230995, 1044685216, 1024578402, 1004899439, 985637565, 966782350, 948323687, 930251780, 912557131, 895230528, 878263040, 861645997, 845370991, 829429859, 813814677, 798517750, 783531608, 768848993, 754462852, 740366335, 726552782, 713015719, 699748851, 686746058, 674001386, 661509042, 649263392, 637258950, 625490379, 613952482, 602640198, 591548600, 580672889, 570008389, 559550544, 549294915, 539237176, 529373110, 519698604, 510209649, 500902337, 491772852]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1027).prefactor = (1242246232322387/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1027).cutoff/(generalMeanRows 1027).c)).2 =
    (336291401908981/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1027).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1027).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1027).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1027

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1027).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1027).criticalRate j.val*(generalMeanRows 1027).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1027).c*(generalMeanRows 1027).criticalPoint j.val)).2-
      (generalMeanRows 1027).J/2-(generalMeanRows 1027).error (generalMeanGrid j.val)+
      (generalMeanRows 1027).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1027).c)).2-
      (generalMeanRows 1027).J/2-(generalMeanRows 1027).error 4 := by
  have he : (generalMeanRows 1027).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1027) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1027)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1027

/-! Kernel-checked entropy margins for general spectral rectangle 1028. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1028
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6378123945, 6190323276, 6009999741, 5836755481, 5670220133, 5510048394, 5355917866, 5207527121, 5064593982, 4926853966, 4794058897, 4665975644, 4542384987, 4423080582, 4307868026, 4196564004, 4088995510, 3984999134, 3884420415, 3787113238, 3692939288, 3601767542, 3513473808, 3427940288, 3345055185, 3264712336, 3186810868, 3111254881, 3037953159, 2966818893, 2897769427, 2830726020, 2765613628, 2702360697, 2640898965, 2581163290, 2523091474, 2466624108, 2411704423, 2358278152, 2306293398, 2255700510, 2206451972, 2158502290, 2111807892, 2066327031, 2022019695, 1978847522, 1936773717, 1895762978, 1855781423, 1816796525, 1778777041, 1741692959, 1705515437, 1670216746, 1635770224, 1602150223, 1569332066, 1537292000, 1506007156, 1475455509, 1445615843, 1416467711, 1387991406, 1360167926, 1332978944, 1306406779, 1280434369, 1255045246, 1230223507, 1205953796, 1182221276, 1159011611, 1136310945, 1114105880, 1092383460, 1071131154, 1050336837, 1029988772, 1010075601, 990586323, 971510287, 952837170, 934556975, 916660007, 899136873, 881978462, 865175937, 848720726, 832604513, 816819225, 801357027, 786210310, 771371686, 756833977, 742590212, 728633613, 714957596, 701555757, 688421872, 675549886, 662933911, 650568217, 638447229, 626565522, 614917812, 603498959, 592303955, 581327922, 570566111, 560013892, 549666755, 539520306, 529570259, 519812438, 510242771, 500857285, 491652107, 482623458, 473767652]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1028).prefactor = (1223074607996291/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1028).cutoff/(generalMeanRows 1028).c)).2 =
    (8757806253773/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1028).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1028).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1028).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1028

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1028).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1028).criticalRate j.val*(generalMeanRows 1028).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1028).c*(generalMeanRows 1028).criticalPoint j.val)).2-
      (generalMeanRows 1028).J/2-(generalMeanRows 1028).error (generalMeanGrid j.val)+
      (generalMeanRows 1028).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1028).c)).2-
      (generalMeanRows 1028).J/2-(generalMeanRows 1028).error 4 := by
  have he : (generalMeanRows 1028).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1028) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1028)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1028

/-! Kernel-checked entropy margins for general spectral rectangle 1029. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1029
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5989842909, 5796934605, 5611916718, 5434371533, 5263909968, 5100169049, 4942809670, 4791514590, 4645986640, 4505947117, 4371134333, 4241302311, 4116219604, 3995668222, 3879442658, 3767349004, 3659204139, 3554834989, 3454077854, 3356777781, 3262787994, 3171969373, 3084189960, 2999324521, 2917254125, 2837865765, 2761052000, 2686710629, 2614744379, 2545060628, 2477571132, 2412191783, 2348842376, 2287446392, 2227930802, 2170225872, 2114264990, 2059984501, 2007323550, 1956223938, 1906629984, 1858488396, 1811748153, 1766360387, 1722278279, 1679456958, 1637853402, 1597426353, 1558136230, 1519945048, 1482816342, 1446715100, 1411607689, 1377461796, 1344246362, 1311931531, 1280488592, 1249889925, 1220108958, 1191120115, 1162898776, 1135421233, 1108664650, 1082607026, 1057227160, 1032504616, 1008419689, 984953378, 962087351, 939803923, 918086025, 896917182, 876281484, 856163570, 836548599, 817422233, 798770615, 780580353, 762838498, 745532528, 728650333, 712180197, 696110784, 680431123, 665130595, 650198917, 635626132, 621402599, 607518974, 593966208, 580735528, 567818432, 555206680, 542892279, 530867480, 519124765, 507656844, 496456640, 485517288, 474832123, 464394677, 454198668, 444237998, 434506744, 424999152, 415709633, 406632756, 397763244, 389095967, 380625940, 372348316, 364258382, 356351554, 348623376, 341069513, 333685745, 326467971, 319412197, 312514537, 305771209, 299178532]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1029).prefactor = (5094252476708089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1029).cutoff/(generalMeanRows 1029).c)).2 =
    (304849876074161/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1029).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1029).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1029).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1029

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1029).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1029).criticalRate j.val*(generalMeanRows 1029).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1029).c*(generalMeanRows 1029).criticalPoint j.val)).2-
      (generalMeanRows 1029).J/2-(generalMeanRows 1029).error (generalMeanGrid j.val)+
      (generalMeanRows 1029).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1029).c)).2-
      (generalMeanRows 1029).J/2-(generalMeanRows 1029).error 4 := by
  have he : (generalMeanRows 1029).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1029) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1029)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1029

/-! Kernel-checked entropy margins for general spectral rectangle 1030. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1030
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6035547785, 5848051980, 5668186210, 5495542180, 5329739807, 5170424734, 5017266118, 4869954659, 4728200829, 4591733287, 4460297447, 4333654190, 4211578695, 4093859381, 3980296943, 3870703477, 3764901676, 3662724103, 3564012517, 3468617260, 3376396692, 3287216668, 3200950059, 3117476314, 3036681042, 2958455642, 2882696945, 2809306892, 2738192229, 2669264229, 2602438427, 2537634375, 2474775417, 2413788477, 2354603858, 2297155055, 2241378588, 2187213831, 2134602864, 2083490329, 2033823297, 1985551138, 1938625407, 1892999730, 1848629698, 1805472770, 1763488182, 1722636852, 1682881306, 1644185594, 1606515219, 1569837064, 1534119332, 1499331477, 1465444151, 1432429145, 1400259337, 1368908642, 1338351965, 1308565157, 1279524970, 1251209019, 1223595742, 1196664367, 1170394874, 1144767963, 1119765024, 1095368106, 1071559892, 1048323666, 1025643297, 1003503204, 981888343, 960784177, 940176661, 920052217, 900397721, 881200479, 862448214, 844129047, 826231483, 808744394, 791657008, 774958892, 758639941, 742690364, 727100673, 711861674, 696964450, 682400359, 668161014, 654238283, 640624275, 627311331, 614292017, 601559117, 589105623, 576924728, 565009822, 553354481, 541952464, 530797703, 519884302, 509206527, 498758803, 488535707, 478531966, 468742446, 459162156, 449786236, 440609956, 431628711, 422838019, 414233514, 405810944, 397566170, 389495155, 381593970, 373858785, 366285867, 358871578]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1030).prefactor = (4997811930880511/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1030).cutoff/(generalMeanRows 1030).c)).2 =
    (84944556826531/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1030).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1030).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1030).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1030

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1030).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1030).criticalRate j.val*(generalMeanRows 1030).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1030).c*(generalMeanRows 1030).criticalPoint j.val)).2-
      (generalMeanRows 1030).J/2-(generalMeanRows 1030).error (generalMeanGrid j.val)+
      (generalMeanRows 1030).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1030).c)).2-
      (generalMeanRows 1030).J/2-(generalMeanRows 1030).error 4 := by
  have he : (generalMeanRows 1030).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1030) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1030)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1030

/-! Kernel-checked entropy margins for general spectral rectangle 1031. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1031
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5912331204, 5731203594, 5557463712, 5390712044, 5230576870, 5076711816, 4928793674, 4786520461, 4649609671, 4517796714, 4390833498, 4268487162, 4150538918, 4036783007, 3927025746, 3821084663, 3718787701, 3619972502, 3524485737, 3432182502, 3342925755, 3256585806, 3173039840, 3092171478, 3013870375, 2938031843, 2864556505, 2793349973, 2724322550, 2657388949, 2592468040, 2529482601, 2468359102, 2409027490, 2351420994, 2295475944, 2241131600, 2188329988, 2137015755, 2087136025, 2038640270, 1991480180, 1945609557, 1900984194, 1857561783, 1815301810, 1774165468, 1734115572, 1695116473, 1657133991, 1620135332, 1584089029, 1548964875, 1514733861, 1481368121, 1448840875, 1417126384, 1386199893, 1356037592, 1326616573, 1297914781, 1269910985, 1242584735, 1215916329, 1189886779, 1164477780, 1139671682, 1115451456, 1091800675, 1068703483, 1046144569, 1024109151, 1002582947, 981552158, 961003447, 940923919, 921301105, 902122943, 883377763, 865054269, 847141528, 829628953, 812506290, 795763604, 779391269, 763379956, 747720620, 732404490, 717423058, 702768071, 688431523, 674405639, 660682876, 647255906, 634117616, 621261093, 608679624, 596366682, 584315927, 572521193, 560976486, 549675975, 538613990, 527785015, 517183683, 506804769, 496643190, 486693996, 476952367, 467413610, 458073154, 448926547, 439969450, 431197636, 422606986, 414193484, 405953215, 397882364, 389977210, 382234123, 374649564]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1031).prefactor = (979854774001817/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1031).cutoff/(generalMeanRows 1031).c)).2 =
    (72611852432017/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1031).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1031).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1031).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1031

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1031).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1031).criticalRate j.val*(generalMeanRows 1031).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1031).c*(generalMeanRows 1031).criticalPoint j.val)).2-
      (generalMeanRows 1031).J/2-(generalMeanRows 1031).error (generalMeanGrid j.val)+
      (generalMeanRows 1031).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1031).c)).2-
      (generalMeanRows 1031).J/2-(generalMeanRows 1031).error 4 := by
  have he : (generalMeanRows 1031).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1031) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1031)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1031

/-! Kernel-checked entropy margins for general spectral rectangle 1032. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1032
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5608268285, 5423162798, 5245798633, 5075758476, 4912653840, 4756122531, 4605826398, 4461449325, 4322695423, 4189287416, 4060965176, 3937484410, 3818615464, 3704142242, 3593861218, 3487580544, 3385119224, 3286306371, 3190980518, 3098988986, 3010187308, 2924438693, 2841613534, 2761588959, 2684248404, 2609481230, 2537182359, 2467251943, 2399595050, 2334121382, 2270744997, 2209384066, 2149960637, 2092400416, 2036632566, 1982589513, 1930206773, 1879422779, 1830178729, 1782418439, 1736088203, 1691136667, 1647514703, 1605175301, 1564073455, 1524166067, 1485411848, 1447771233, 1411206288, 1375680641, 1341159398, 1307609073, 1274997527, 1243293896, 1212468536, 1182492966, 1153339811, 1124982754, 1097396488, 1070556667, 1044439865, 1019023536, 994285973, 970206269, 946764288, 923940625, 901716580, 880074123, 858995868, 838465046, 818465477, 798981547, 779998186, 761500841, 743475460, 725908468, 708786748, 692097627, 675828851, 659968575, 644505343, 629428074, 614726048, 600388892, 586406564, 572769346, 559467826, 546492888, 533835705, 521487723, 509440652, 497686461, 486217361, 475025803, 464104465, 453446246, 443044258, 432891818, 422982439, 413309829, 403867877, 394650651, 385652393, 376867508, 368290565, 359916285, 351739540, 343755349, 335958870, 328345395, 320910349, 313649285, 306557877, 299631918, 292867319, 286260099, 279806388, 273502418, 267344525, 261329141, 255452797]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1032).prefactor = (5077359558728903/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1032).cutoff/(generalMeanRows 1032).c)).2 =
    (65180657054399/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1032).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1032).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1032).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1032

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1032).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1032).criticalRate j.val*(generalMeanRows 1032).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1032).c*(generalMeanRows 1032).criticalPoint j.val)).2-
      (generalMeanRows 1032).J/2-(generalMeanRows 1032).error (generalMeanGrid j.val)+
      (generalMeanRows 1032).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1032).c)).2-
      (generalMeanRows 1032).J/2-(generalMeanRows 1032).error 4 := by
  have he : (generalMeanRows 1032).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1032) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1032)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1032

/-! Kernel-checked entropy margins for general spectral rectangle 1033. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1033
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5649095839, 5469805657, 5297956648, 5133143202, 4974988010, 4823139574, 4677269996, 4537072996, 4402262139, 4272569240, 4147742922, 4027547325, 3911760920, 3800175448, 3692594949, 3588834874, 3488721276, 3392090079, 3298786390, 3208663885, 3121584238, 3037416590, 2956037071, 2877328345, 2801179206, 2727484188, 2656143212, 2587061262, 2520148072, 2455317851, 2392489013, 2331583934, 2272528721, 2215253002, 2159689723, 2105774965, 2053447766, 2002649961, 1953326029, 1905422949, 1858890067, 1813678969, 1769743364, 1727038971, 1685523420, 1645156146, 1605898304, 1567712679, 1530563602, 1494416877, 1459239707, 1425000625, 1391669426, 1359217114, 1327615837, 1296838834, 1266860385, 1237655764, 1209201187, 1181473775, 1154451506, 1128113183, 1102438392, 1077407466, 1053001458, 1029202102, 1005991787, 983353528, 961270939, 939728207, 918710067, 898201781, 878189111, 858658306, 839596075, 820989569, 802826368, 785094459, 767782219, 750878403, 734372128, 718252857, 702510387, 687134835, 672116629, 657446490, 643115428, 629114725, 615435929, 602070844, 589011516, 576250231, 563779499, 551592054, 539680839, 528039002, 516659888, 505537034, 494664159, 484035159, 473644103, 463485224, 453552917, 443841730, 434346361, 425061652, 415982587, 407104282, 398421987, 389931077, 381627051, 373505527, 365562235, 357793022, 350193838, 342760741, 335489889, 328377540, 321420047, 314613855, 307955499]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1033).prefactor = (4963118744112289/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1033).cutoff/(generalMeanRows 1033).c)).2 =
    (362848979328901/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1033).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1033).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1033).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1033

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1033).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1033).criticalRate j.val*(generalMeanRows 1033).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1033).c*(generalMeanRows 1033).criticalPoint j.val)).2-
      (generalMeanRows 1033).J/2-(generalMeanRows 1033).error (generalMeanGrid j.val)+
      (generalMeanRows 1033).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1033).c)).2-
      (generalMeanRows 1033).J/2-(generalMeanRows 1033).error 4 := by
  have he : (generalMeanRows 1033).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1033) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1033)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1033

/-! Kernel-checked entropy margins for general spectral rectangle 1034. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1034
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5508083091, 5324584273, 5148835560, 4980415115, 4818930392, 4664015570, 4515329265, 4372552486, 4235386802, 4103552694, 3976788070, 3854846925, 3737498119, 3624524283, 3515720809, 3410894936, 3309864917, 3212459255, 3118515999, 3027882107, 2940412850, 2855971274, 2774427690, 2695659221, 2619549367, 2545987611, 2474869053, 2406094068, 2339567993, 2275200827, 2212906965, 2152604938, 2094217178, 2037669793, 1982892366, 1929817757, 1878381924, 1828523753, 1780184899, 1733309639, 1687844731, 1643739284, 1600944636, 1559414235, 1519103536, 1479969892, 1441972464, 1405072127, 1369231387, 1334414298, 1300586386, 1267714581, 1235767145, 1204713613, 1174524726, 1145172380, 1116629569, 1088870337, 1061869723, 1035603724, 1010049244, 985184058, 960986770, 937436779, 914514240, 892200036, 870475740, 849323591, 828726461, 808667832, 789131767, 770102886, 751566345, 733507811, 715913442, 698769870, 682064174, 665783872, 649916894, 634451573, 619376624, 604681132, 590354536, 576386618, 562767486, 549487562, 536537575, 523908542, 511591765, 499578814, 487861520, 476431965, 465282475, 454405608, 443794145, 433441086, 423339641, 413483219, 403865426, 394480055, 385321082, 376382656, 367659097, 359144888, 350834670, 342723238, 334805534, 327076641, 319531784, 312166318, 304975730, 297955631, 291101754, 284409949, 277876178, 271496515, 265267141, 259184339, 253244493, 247444083, 241779683]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1034).prefactor = (2566395378960549/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1034).cutoff/(generalMeanRows 1034).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1034).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1034).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1034).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1034

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1034).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1034).criticalRate j.val*(generalMeanRows 1034).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1034).c*(generalMeanRows 1034).criticalPoint j.val)).2-
      (generalMeanRows 1034).J/2-(generalMeanRows 1034).error (generalMeanGrid j.val)+
      (generalMeanRows 1034).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1034).c)).2-
      (generalMeanRows 1034).J/2-(generalMeanRows 1034).error 4 := by
  have he : (generalMeanRows 1034).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1034) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1034)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1034

/-! Kernel-checked entropy margins for general spectral rectangle 1035. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1035
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5696385567, 5506613554, 5324856595, 5150678432, 4983673100, 4823462272, 4669692892, 4522035064, 4380180156, 4243839092, 4112740820, 3986630925, 3865270366, 3748434342, 3635911250, 3527501739, 3423017851, 3322282223, 3225127369, 3131395015, 3040935485, 2953607140, 2869275861, 2787814568, 2709102779, 2633026198, 2559476340, 2488350175, 2419549801, 2352982143, 2288558668, 2226195121, 2165811283, 2107330737, 2050680658, 1995791610, 1942597362, 1891034711, 1841043317, 1792565553, 1745546355, 1699933095, 1655675444, 1612725262, 1571036477, 1530564988, 1491268558, 1453106726, 1416040714, 1380033347, 1345048975, 1311053396, 1278013787, 1245898641, 1214677699, 1184321897, 1154803306, 1126095081, 1098171409, 1071007465, 1044579365, 1018864123, 993839613, 969484528, 945778347, 922701296, 900234321, 878359052, 857057777, 836313413, 816109476, 796430063, 777259821, 758583928, 740388068, 722658416, 705381610, 688544740, 672135324, 656141297, 640550987, 625353106, 610536734, 596091301, 582006577, 568272658, 554879955, 541819179, 529081333, 516657700, 504539832, 492719541, 481188888, 469940178, 458965945, 448258951, 437812172, 427618793, 417672200, 407965976, 398493889, 389249889, 380228101, 371422820, 362828505, 354439771, 346251387, 338258270, 330455480, 322838214, 315401805, 308141713, 301053525, 294132950, 287375812, 280778050, 274335715, 268044963, 261902054, 255903347, 250045302]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1035).prefactor = (5308263276161539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1035).cutoff/(generalMeanRows 1035).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1035).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1035).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1035).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1035

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1035).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1035).criticalRate j.val*(generalMeanRows 1035).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1035).c*(generalMeanRows 1035).criticalPoint j.val)).2-
      (generalMeanRows 1035).J/2-(generalMeanRows 1035).error (generalMeanGrid j.val)+
      (generalMeanRows 1035).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1035).c)).2-
      (generalMeanRows 1035).J/2-(generalMeanRows 1035).error 4 := by
  have he : (generalMeanRows 1035).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1035) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1035)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1035

/-! Kernel-checked entropy margins for general spectral rectangle 1036. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1036
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5891125460, 5694865792, 5506895186, 5326762469, 5154047797, 4988359909, 4829333682, 4676627939, 4529923498, 4388921400, 4253341328, 4122920168, 3997410707, 3876580460, 3760210590, 3648094930, 3540039095, 3435859661, 3335383416, 3238446674, 3144894643, 3054580841, 2967366565, 2883120390, 2801717714, 2723040337, 2646976061, 2573418336, 2502265913, 2433422535, 2366796642, 2302301100, 2239852945, 2179373150, 2120786398, 2064020882, 2009008106, 1955682704, 1903982276, 1853847223, 1805220601, 1758047979, 1712277311, 1667858809, 1624744828, 1582889757, 1542249918, 1502783463, 1464450291, 1427211956, 1391031588, 1355873816, 1321704697, 1288491644, 1256203365, 1224809802, 1194282072, 1164592410, 1135714124, 1107621538, 1080289952, 1053695594, 1027815582, 1002627881, 978111266, 954245290, 931010246, 908387137, 886357644, 864904101, 844009461, 823657276, 803831670, 784517311, 765699398, 747363629, 729496189, 712083724, 695113327, 678572518, 662449229, 646731785, 631408892, 616469619, 601903386, 587699952, 573849398, 560342119, 547168810, 534320456, 521788319, 509563933, 497639086, 486005821, 474656417, 463583388, 452779469, 442237613, 431950981, 421912934, 412117028, 402557008, 393226796, 384120493, 375232367, 366556851, 358088535, 349822160, 341752620, 333874946, 326184311, 318676022, 311345513, 304188347, 297200205, 290376889, 283714313, 277208502, 270855587, 264651805, 258593493]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1036).prefactor = (2744867299096547/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1036).cutoff/(generalMeanRows 1036).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1036).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1036).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1036).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1036

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1036).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1036).criticalRate j.val*(generalMeanRows 1036).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1036).c*(generalMeanRows 1036).criticalPoint j.val)).2-
      (generalMeanRows 1036).J/2-(generalMeanRows 1036).error (generalMeanGrid j.val)+
      (generalMeanRows 1036).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1036).c)).2-
      (generalMeanRows 1036).J/2-(generalMeanRows 1036).error 4 := by
  have he : (generalMeanRows 1036).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1036) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1036)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1036

/-! Kernel-checked entropy margins for general spectral rectangle 1037. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1037
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6182423662, 5978881658, 5783897914, 5597006512, 5417773925, 5245796176, 5080696304, 4922122110, 4769744118, 4623253764, 4482361741, 4346796526, 4216303025, 4090641359, 3969585752, 3852923519, 3740454141, 3631988424, 3527347719, 3426363217, 3328875292, 3234732899, 3143793023, 3055920163, 2970985863, 2888868272, 2809451736, 2732626426, 2658287986, 2586337208, 2516679732, 2449225762, 2383889804, 2320590422, 2259250009, 2199794574, 2142153540, 2086259561, 2032048343, 1979458481, 1928431305, 1878910736, 1830843152, 1784177256, 1738863960, 1694856270, 1652109182, 1610579580, 1570226142, 1531009254, 1492890923, 1455834698, 1419805597, 1384770038, 1350695768, 1317551805, 1285308374, 1253936854, 1223409722, 1193700508, 1164783738, 1136634898, 1109230386, 1082547473, 1056564262, 1031259656, 1006613318, 982605643, 959217721, 936431313, 914228819, 892593253, 871508215, 850957869, 830926919, 811400586, 792364590, 773805124, 755708843, 738062839, 720854626, 704072126, 687703647, 671737875, 656163856, 640970980, 626148975, 611687885, 597578068, 583810175, 570375148, 557264200, 544468815, 531980732, 519791935, 507894650, 496281330, 484944653, 473877510, 463072998, 452524415, 442225251, 432169185, 422350072, 412761944, 403399000, 394255604, 385326274, 376605684, 368088651, 359770139, 351645247, 343709209, 335957388, 328385273, 320988473, 313762716, 306703844, 299807809, 293070669, 286488589]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1037).prefactor = (567740980255049/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1037).cutoff/(generalMeanRows 1037).c)).2 =
    (344721594736347/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1037).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1037).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1037).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1037

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1037).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1037).criticalRate j.val*(generalMeanRows 1037).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1037).c*(generalMeanRows 1037).criticalPoint j.val)).2-
      (generalMeanRows 1037).J/2-(generalMeanRows 1037).error (generalMeanGrid j.val)+
      (generalMeanRows 1037).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1037).c)).2-
      (generalMeanRows 1037).J/2-(generalMeanRows 1037).error 4 := by
  have he : (generalMeanRows 1037).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1037) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1037)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1037

/-! Kernel-checked entropy margins for general spectral rectangle 1038. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1038
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6488452590, 6277387695, 6075158341, 5881283369, 5695315108, 5516836436, 5345458166, 5180816704, 5022571948, 4870405406, 4724018495, 4583131007, 4447479712, 4316817104, 4190910246, 4069539728, 3952498707, 3839592039, 3730635474, 3625454919, 3523885770, 3425772282, 3330967000, 3239330230, 3150729546, 3065039341, 2982140408, 2901919548, 2824269210, 2749087156, 2676276148, 2605743656, 2537401590, 2471166042, 2406957056, 2344698403, 2284317373, 2225744587, 2168913814, 2113761798, 2060228105, 2008254969, 1957787154, 1908771821, 1861158406, 1814898503, 1769945755, 1726255747, 1683785916, 1642495451, 1602345214, 1563297655, 1525316734, 1488367851, 1452417775, 1417434583, 1383387592, 1350247308, 1317985366, 1286574483, 1255988402, 1226201851, 1197190499, 1168930907, 1141400499, 1114577515, 1088440979, 1062970667, 1038147070, 1013951367, 990365395, 967371622, 944953117, 923093530, 901777064, 880988456, 860712952, 840936288, 821644671, 802824759, 784463644, 766548834, 749068239, 732010152, 715363237, 699116516, 683259351, 667781435, 652672778, 637923698, 623524803, 609466990, 595741425, 582339541, 569253023, 556473802, 543994045, 531806150, 519902731, 508276618, 496920844, 485828644, 474993441, 464408846, 454068647, 443966807, 434097455, 424454884, 415033541, 405828027, 396833089, 388043616, 379454636, 371061308, 362858922, 354842892, 347008755, 339352163, 331868885, 324554798, 317405888]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1038).prefactor = (2935750489350221/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1038).cutoff/(generalMeanRows 1038).c)).2 =
    (350727618796559/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1038).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1038).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1038).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1038

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1038).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1038).criticalRate j.val*(generalMeanRows 1038).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1038).c*(generalMeanRows 1038).criticalPoint j.val)).2-
      (generalMeanRows 1038).J/2-(generalMeanRows 1038).error (generalMeanGrid j.val)+
      (generalMeanRows 1038).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1038).c)).2-
      (generalMeanRows 1038).J/2-(generalMeanRows 1038).error 4 := by
  have he : (generalMeanRows 1038).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1038) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1038)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1038

/-! Kernel-checked entropy margins for general spectral rectangle 1039. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1039
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7001509788, 6784880971, 6577169089, 6377887411, 6186583252, 6002834973, 5826249322, 5656459044, 5493120746, 5335912976, 5184534490, 5038702693, 4898152215, 4762633633, 4631912298, 4505767270, 4383990347, 4266385176, 4152766433, 4042959083, 3936797687, 3834125770, 3734795242, 3638665853, 3545604703, 3455485778, 3368189521, 3283602443, 3201616753, 3122130014, 3045044833, 2970268559, 2897713009, 2827294215, 2758932181, 2692550660, 2628076945, 2565441674, 2504578644, 2445424644, 2387919287, 2332004867, 2277626212, 2224730551, 2173267392, 2123188402, 2074447296, 2026999735, 1980803226, 1935817030, 1892002075, 1849320874, 1807737447, 1767217251, 1727727104, 1689235126, 1651710676, 1615124292, 1579447636, 1544653443, 1510715473, 1477608460, 1445308071, 1413790862, 1383034242, 1353016430, 1323716422, 1295113959, 1267189490, 1239924145, 1213299704, 1187298572, 1161903750, 1137098810, 1112867874, 1089195588, 1066067105, 1043468057, 1021384546, 999803115, 978710737, 958094796, 937943071, 918243721, 898985270, 880156593, 861746904, 843745740, 826142954, 808928698, 792093416, 775627831, 759522935, 743769983, 728360477, 713286163, 698539021, 684111254, 669995285, 656183745, 642669470, 629445490, 616505026, 603841481, 591448436, 579319643, 567449020, 555830646, 544458753, 533327726, 522432094, 511766528, 501325836, 491104956, 481098957, 471303033, 461712495, 452322775, 443129417, 434128074, 425314509]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1039).prefactor = (2985510405012273/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1039).cutoff/(generalMeanRows 1039).c)).2 =
    (187559535960359/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1039).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1039).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1039).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1039

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1039).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1039).criticalRate j.val*(generalMeanRows 1039).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1039).c*(generalMeanRows 1039).criticalPoint j.val)).2-
      (generalMeanRows 1039).J/2-(generalMeanRows 1039).error (generalMeanGrid j.val)+
      (generalMeanRows 1039).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1039).c)).2-
      (generalMeanRows 1039).J/2-(generalMeanRows 1039).error 4 := by
  have he : (generalMeanRows 1039).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1039) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1039)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1039

/-! Kernel-checked entropy margins for general spectral rectangle 1040. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1040
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7276148825, 7073014077, 6877662101, 6689689098, 6508719008, 6334401031, 6166407425, 6004431547, 5848186102, 5697401575, 5551824824, 5411217810, 5275356455, 5144029600, 5017038070, 4894193814, 4775319129, 4660245949, 4548815190, 4440876157, 4336285995, 4234909188, 4136617091, 4041287503, 3948804276, 3859056943, 3771940384, 3687354509, 3605203967, 3525397873, 3447849560, 3372476336, 3299199271, 3227942989, 3158635476, 3091207899, 3025594441, 2961732143, 2899560754, 2839022592, 2780062417, 2722627306, 2666666536, 2612131479, 2558975496, 2507153844, 2456623581, 2407343483, 2359273963, 2312376989, 2266616019, 2221955928, 2178362941, 2135804577, 2094249585, 2053667894, 2014030554, 1975309694, 1937478467, 1900511012, 1864382405, 1829068624, 1794546506, 1760793714, 1727788701, 1695510675, 1663939569, 1633056010, 1602841293, 1573277351, 1544346729, 1516032560, 1488318542, 1461188913, 1434628434, 1408622362, 1383156436, 1358216856, 1333790263, 1309863728, 1286424727, 1263461133, 1240961197, 1218913536, 1197307115, 1176131239, 1155375539, 1135029957, 1115084738, 1095530418, 1076357812, 1057558008, 1039122350, 1021042437, 1003310107, 985917435, 968856718, 952120473, 935701426, 919592505, 903786836, 888277732, 873058691, 858123384, 843465657, 829079517, 814959134, 801098829, 787493075, 774136488, 761023824, 748149973, 735509958, 723098928, 710912154, 698945026, 687193051, 675651844, 664317131, 653184744, 642250612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1040).prefactor = (5044262486406209/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1040).cutoff/(generalMeanRows 1040).c)).2 =
    (10196568978501/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1040).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1040).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1040).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1040

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1040).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1040).criticalRate j.val*(generalMeanRows 1040).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1040).c*(generalMeanRows 1040).criticalPoint j.val)).2-
      (generalMeanRows 1040).J/2-(generalMeanRows 1040).error (generalMeanGrid j.val)+
      (generalMeanRows 1040).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1040).c)).2-
      (generalMeanRows 1040).J/2-(generalMeanRows 1040).error 4 := by
  have he : (generalMeanRows 1040).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1040) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1040)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1040

/-! Kernel-checked entropy margins for general spectral rectangle 1041. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1041
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7019045567, 6822045391, 6632658813, 6450487608, 6275160964, 6106333038, 5943680790, 5786902051, 5635713793, 5489850584, 5349063197, 5213117357, 5081792606, 4954881280, 4832187578, 4713526711, 4598724136, 4487614848, 4380042733, 4275859981, 4174926537, 4077109606, 3982283191, 3890327669, 3801129394, 3714580341, 3630577765, 3549023889, 3469825613, 3392894250, 3318145266, 3245498056, 3174875715, 3106204845, 3039415355, 2974440289, 2911215656, 2849680276, 2789775631, 2731445726, 2674636963, 2619298020, 2565379731, 2512834983, 2461618614, 2411687315, 2362999543, 2315515433, 2269196719, 2224006658, 2179909957, 2136872708, 2094862320, 2053847461, 2013797999, 1974684949, 1936480419, 1899157562, 1862690530, 1827054428, 1792225276, 1758179965, 1724896220, 1692352566, 1660528292, 1629403419, 1598958669, 1569175437, 1540035758, 1511522287, 1483618269, 1456307517, 1429574387, 1403403757, 1377781007, 1352691996, 1328123047, 1304060925, 1280492820, 1257406335, 1234789462, 1212630574, 1190918408, 1169642049, 1148790920, 1128354767, 1108323649, 1088687923, 1069438237, 1050565518, 1032060957, 1013916009, 996122374, 978671993, 961557039, 944769910, 928303215, 912149776, 896302611, 880754935, 865500149, 850531834, 835843746, 821429809, 807284111, 793400896, 779774561, 766399650, 753270850, 740382986, 727731014, 715310021, 703115220, 691141941, 679385635, 667841864, 656506302, 645374728, 634443024, 623707172, 613163254]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1041).prefactor = (9698242317277/1953125000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1041).cutoff/(generalMeanRows 1041).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1041).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1041).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1041).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1041

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1041).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1041).criticalRate j.val*(generalMeanRows 1041).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1041).c*(generalMeanRows 1041).criticalPoint j.val)).2-
      (generalMeanRows 1041).J/2-(generalMeanRows 1041).error (generalMeanGrid j.val)+
      (generalMeanRows 1041).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1041).c)).2-
      (generalMeanRows 1041).J/2-(generalMeanRows 1041).error 4 := by
  have he : (generalMeanRows 1041).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1041) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1041)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1041

/-! Kernel-checked entropy margins for general spectral rectangle 1042. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1042
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6750618852, 6545304432, 6348088852, 6158551161, 5976299184, 5800966967, 5632212508, 5469715731, 5313176677, 5162313887, 5016862938, 4876575136, 4741216326, 4610565816, 4484415406, 4362568497, 4244839279, 4131051997, 4021040275, 3914646487, 3811721199, 3712122636, 3615716202, 3522374035, 3431974596, 3344402283, 3259547084, 3177304245, 3097573966, 3020261119, 2945274985, 2872529005, 2801940554, 2733430723, 2666924124, 2602348695, 2539635534, 2478718725, 2419535188, 2362024536, 2306128934, 2251792973, 2198963550, 2147589755, 2097622761, 2049015725, 2001723694, 1955703512, 1910913737, 1867314562, 1824867736, 1783536493, 1743285488, 1704080726, 1665889506, 1628680360, 1592423001, 1557088269, 1522648083, 1489075391, 1456344130, 1424429180, 1393306324, 1362952214, 1333344327, 1304460937, 1276281079, 1248784519, 1221951720, 1195763821, 1170202601, 1145250460, 1120890391, 1097105956, 1073881265, 1051200954, 1029050165, 1007414523, 986280122, 965633505, 945461646, 925751935, 906492160, 887670497, 869275489, 851296037, 833721385, 816541109, 799745102, 783323566, 767266998, 751566180, 736212170, 721196293, 706510127, 692145500, 678094477, 664349355, 650902650, 637747098, 624875637, 612281408, 599957747, 587898174, 576096393, 564546281, 553241883, 542177412, 531347235, 520745873, 510367997, 500208420, 490262094, 480524106, 470989673, 461654138, 452512966, 443561740, 434796161, 426212036, 417805284]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1042).prefactor = (2608182308626923/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1042).cutoff/(generalMeanRows 1042).c)).2 =
    (74551333338873/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1042).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1042).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1042).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1042

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1042).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1042).criticalRate j.val*(generalMeanRows 1042).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1042).c*(generalMeanRows 1042).criticalPoint j.val)).2-
      (generalMeanRows 1042).J/2-(generalMeanRows 1042).error (generalMeanGrid j.val)+
      (generalMeanRows 1042).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1042).c)).2-
      (generalMeanRows 1042).J/2-(generalMeanRows 1042).error 4 := by
  have he : (generalMeanRows 1042).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1042) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1042)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1042

/-! Kernel-checked entropy margins for general spectral rectangle 1043. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1043
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6683476799, 6484649839, 6293673673, 6110136037, 5933652996, 5763866437, 5600441830, 5443066243, 5291446562, 5145307890, 5004392119, 4868456629, 4737273122, 4610626560, 4488314201, 4370144724, 4255937433, 4145521519, 4038735399, 3935426098, 3835448689, 3738665772, 3644946998, 3554168628, 3466213126, 3380968781, 3298329359, 3218193776, 3140465800, 3065053769, 2991870333, 2920832205, 2851859942, 2784877727, 2719813174, 2656597143, 2595163564, 2535449279, 2477393885, 2420939593, 2366031095, 2312615435, 2260641892, 2210061867, 2160828781, 2112897969, 2066226593, 2020773551, 1976499394, 1933366247, 1891337734, 1850378909, 1810456188, 1771537289, 1733591167, 1696587964, 1660498949, 1625296472, 1590953914, 1557445641, 1524746963, 1492834088, 1461684088, 1431274858, 1401585084, 1372594208, 1344282393, 1316630497, 1289620044, 1263233192, 1237452711, 1212261957, 1187644846, 1163585834, 1140069894, 1117082497, 1094609589, 1072637574, 1051153298, 1030144028, 1009597439, 989501595, 969844939, 950616273, 931804747, 913399848, 895391383, 877769471, 860524529, 843647264, 827128657, 810959959, 795132680, 779638574, 764469641, 749618106, 735076423, 720837257, 706893483, 693238176, 679864607, 666766231, 653936686, 641369785, 629059508, 617000003, 605185570, 593610666, 582269895, 571158004, 560269878, 549600537, 539145130, 528898931, 518857338, 509015865, 499370142, 489915907, 480649009, 471565398, 462661127]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1043).prefactor = (2556585152110743/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1043).cutoff/(generalMeanRows 1043).c)).2 =
    (81417800971937/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1043).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1043).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1043).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1043

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1043).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1043).criticalRate j.val*(generalMeanRows 1043).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1043).c*(generalMeanRows 1043).criticalPoint j.val)).2-
      (generalMeanRows 1043).J/2-(generalMeanRows 1043).error (generalMeanGrid j.val)+
      (generalMeanRows 1043).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1043).c)).2-
      (generalMeanRows 1043).J/2-(generalMeanRows 1043).error 4 := by
  have he : (generalMeanRows 1043).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1043) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1043)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1043

/-! Kernel-checked entropy margins for general spectral rectangle 1044. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1044
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6529195143, 6337194136, 6152805740, 5975626080, 5805279177, 5641414475, 5483704654, 5331843664, 5185544980, 5044540028, 4908576767, 4777418420, 4650842311, 4528638829, 4410610466, 4296570963, 4186344511, 4079765037, 3976675537, 3876927474, 3780380222, 3686900547, 3596362143, 3508645191, 3423635957, 3341226420, 3261313925, 3183800864, 3108594378, 3035606078, 2964751791, 2895951315, 2829128201, 2764209537, 2701125759, 2639810463, 2580200238, 2522234501, 2465855354, 2411007434, 2357637789, 2305695748, 2255132805, 2205902513, 2157960374, 2111263748, 2065771756, 2021445196, 1978246462, 1936139463, 1895089554, 1855063466, 1816029241, 1777956169, 1740814730, 1704576543, 1669214307, 1634701756, 1601013614, 1568125543, 1536014109, 1504656737, 1474031675, 1444117959, 1414895374, 1386344427, 1358446315, 1331182891, 1304536643, 1278490661, 1253028617, 1228134737, 1203793780, 1179991016, 1156712205, 1133943576, 1111671810, 1089884021, 1068567739, 1047710893, 1027301796, 1007329131, 987781934, 968649583, 949921783, 931588556, 913640226, 896067410, 878861007, 862012186, 845512378, 829353265, 813526771, 798025054, 782840499, 767965704, 753393482, 739116846, 725129002, 711423349, 697993465, 684833104, 671936192, 659296817, 646909227, 634767824, 622867156, 611201916, 599766937, 588557185, 577567756, 566793874, 556230881, 545874242, 535719532, 525762440, 515998761, 506424395, 497035343, 487827703, 478797668]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1044).prefactor = (5010098897659089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1044).cutoff/(generalMeanRows 1044).c)).2 =
    (69513521151863/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1044).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1044).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1044).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1044

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1044).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1044).criticalRate j.val*(generalMeanRows 1044).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1044).c*(generalMeanRows 1044).criticalPoint j.val)).2-
      (generalMeanRows 1044).J/2-(generalMeanRows 1044).error (generalMeanGrid j.val)+
      (generalMeanRows 1044).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1044).c)).2-
      (generalMeanRows 1044).J/2-(generalMeanRows 1044).error 4 := by
  have he : (generalMeanRows 1044).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1044) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1044)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1044

/-! Kernel-checked entropy margins for general spectral rectangle 1045. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1045
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6291760320, 6106793672, 5929211260, 5758617466, 5594644130, 5436948126, 5285209205, 5139128069, 4998424644, 4862836536, 4732117637, 4606036863, 4484377019, 4366933766, 4253514683, 4143938411, 4038033877, 3935639576, 3836602925, 3740779656, 3648033272, 3558234537, 3471261013, 3386996623, 3305331259, 3226160409, 3149384817, 3074910169, 3002646793, 2932509391, 2864416779, 2798291657, 2734060382, 2671652761, 2611001865, 2552043842, 2494717751, 2438965405, 2384731220, 2331962079, 2280607203, 2230618024, 2181948073, 2134552875, 2088389839, 2043418172, 1999598783, 1956894199, 1915268485, 1874687172, 1835117179, 1796526752, 1758885397, 1722163820, 1686333874, 1651368500, 1617241678, 1583928381, 1551404528, 1519646939, 1488633298, 1458342111, 1428752669, 1399845015, 1371599913, 1343998809, 1317023809, 1290657648, 1264883660, 1239685756, 1215048401, 1190956584, 1167395804, 1144352044, 1121811752, 1099761822, 1078189579, 1057082754, 1036429478, 1016218257, 996437962, 977077815, 958127370, 939576509, 921415421, 903634594, 886224806, 869177109, 852482821, 836133519, 820121025, 804437399, 789074930, 774026130, 759283722, 744840635, 730689997, 716825126, 703239527, 689926882, 676881044, 664096035, 651566035, 639285381, 627248561, 615450206, 603885090, 592548119, 581434336, 570538907, 559857122, 549384392, 539116242, 529048311, 519176343, 509496190, 500003806, 490695243, 481566649, 472614266, 463834425]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1045).prefactor = (4906759121548101/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1045).cutoff/(generalMeanRows 1045).c)).2 =
    (364149618355453/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1045).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1045).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1045).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1045

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1045).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1045).criticalRate j.val*(generalMeanRows 1045).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1045).c*(generalMeanRows 1045).criticalPoint j.val)).2-
      (generalMeanRows 1045).J/2-(generalMeanRows 1045).error (generalMeanGrid j.val)+
      (generalMeanRows 1045).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1045).c)).2-
      (generalMeanRows 1045).J/2-(generalMeanRows 1045).error 4 := by
  have he : (generalMeanRows 1045).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1045) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1045)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1045

/-! Kernel-checked entropy margins for general spectral rectangle 1046. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1046
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6170987956, 5979818402, 5796397297, 5620311029, 5451174553, 5288628873, 5132338802, 4981990964, 4837291999, 4697966960, 4563757862, 4434422376, 4309732649, 4189474227, 4073445083, 3961454731, 3853323409, 3748881349, 3647968087, 3550431848, 3456128973, 3364923388, 3276686124, 3191294866, 3108633538, 3028591921, 2951065300, 2875954129, 2803163729, 2732604001, 2664189164, 2597837504, 2533471148, 2471015844, 2410400765, 2351558319, 2294423972, 2238936086, 2185035763, 2132666701, 2081775056, 2032309318, 1984220189, 1937460469, 1891984952, 1847750326, 1804715076, 1762839400, 1722085120, 1682415607, 1643795705, 1606191658, 1569571049, 1533902733, 1499156776, 1465304405, 1432317948, 1400170786, 1368837307, 1338292856, 1308513699, 1279476974, 1251160658, 1223543530, 1196605133, 1170325742, 1144686334, 1119668559, 1095254706, 1071427682, 1048170983, 1025468671, 1003305349, 981666140, 960536667, 939903029, 919751785, 900069937, 880844908, 862064528, 843717018, 825790975, 808275357, 791159470, 774432951, 758085762, 742108173, 726490751, 711224351, 696300103, 681709403, 667443905, 653495510, 639856354, 626518807, 613475459, 600719113, 588242779, 576039667, 564103178, 552426901, 541004603, 529830223, 518897870, 508201815, 497736485, 487496457, 477476457, 467671351, 458076144, 448685973, 439496103, 430501925, 421698948, 413082802, 404649226, 396394072, 388313296, 380402959, 372659222, 365078341]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1046).prefactor = (5105763409703809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1046).cutoff/(generalMeanRows 1046).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1046).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1046).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1046).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1046

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1046).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1046).criticalRate j.val*(generalMeanRows 1046).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1046).c*(generalMeanRows 1046).criticalPoint j.val)).2-
      (generalMeanRows 1046).J/2-(generalMeanRows 1046).error (generalMeanGrid j.val)+
      (generalMeanRows 1046).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1046).c)).2-
      (generalMeanRows 1046).J/2-(generalMeanRows 1046).error 4 := by
  have he : (generalMeanRows 1046).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1046) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1046)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1046

/-! Kernel-checked entropy margins for general spectral rectangle 1047. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1047
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6025048241, 5841155893, 5664732437, 5495374810, 5332707985, 5176382508, 5026072290, 4881472651, 4742298558, 4608283043, 4479175781, 4354741805, 4234760337, 4119023738, 4007336548, 3899514605, 3795384255, 3694781616, 3597551912, 3503548859, 3412634101, 3324676691, 3239552614, 3157144341, 3077340429, 3000035134, 2925128067, 2852523870, 2782131910, 2713866004, 2647644154, 2583388306, 2521024128, 2460480790, 2401690774, 2344589688, 2289116091, 2235211336, 2182819414, 2131886818, 2082362404, 2034197271, 1987344643, 1941759754, 1897399754, 1854223601, 1812191979, 1771267203, 1731413143, 1692595148, 1654779969, 1617935693, 1582031681, 1547038503, 1512927881, 1479672640, 1447246647, 1415624772, 1384782835, 1354697564, 1325346558, 1296708241, 1268761830, 1241487295, 1214865332, 1188877325, 1163505322, 1138731998, 1114540637, 1090915101, 1067839806, 1045299700, 1023280238, 1001767365, 980747494, 960207485, 940134631, 920516635, 901341600, 882598007, 864274705, 846360893, 828846110, 811720217, 794973390, 778596105, 762579126, 746913496, 731590527, 716601789, 701939099, 687594515, 673560327, 659829045, 646393396, 633246314, 620380932, 607790576, 595468760, 583409177, 571605692, 560052341, 548743320, 537672983, 526835835, 516226529, 505839859, 495670757, 485714286, 475965641, 466420138, 457073217, 447920433, 438957455, 430180062, 421584139, 413165674, 404920757, 396845572, 388936401, 381189614]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1047).prefactor = (4985064449104499/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1047).cutoff/(generalMeanRows 1047).c)).2 =
    (363292536665959/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1047).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1047).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1047).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1047

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1047).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1047).criticalRate j.val*(generalMeanRows 1047).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1047).c*(generalMeanRows 1047).criticalPoint j.val)).2-
      (generalMeanRows 1047).J/2-(generalMeanRows 1047).error (generalMeanGrid j.val)+
      (generalMeanRows 1047).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1047).c)).2-
      (generalMeanRows 1047).J/2-(generalMeanRows 1047).error 4 := by
  have he : (generalMeanRows 1047).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1047) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1047)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1047

/-! Kernel-checked entropy margins for general spectral rectangle 1048. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1048
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5811024338, 5622285785, 5441374319, 5267868759, 5101377042, 4941533669, 4787997426, 4640449349, 4498590905, 4362142350, 4230841256, 4104441178, 3982710450, 3865431086, 3752397788, 3643417040, 3538306278, 3436893132, 3339014738, 3244517093, 3153254477, 3065088913, 2979889667, 2897532792, 2817900704, 2740881790, 2666370045, 2594264732, 2524470071, 2456894949, 2391452645, 2328060581, 2266640084, 2207116169, 2149417330, 2093475352, 2039225127, 1986604491, 1935554061, 1886017090, 1837939330, 1791268897, 1745956153, 1701953588, 1659215715, 1617698965, 1577361592, 1538163581, 1500066568, 1463033754, 1427029831, 1392020909, 1357974454, 1324859215, 1292645170, 1261303468, 1230806372, 1201127210, 1172240327, 1144121035, 1116745575, 1090091072, 1064135496, 1038857626, 1014237013, 990253950, 966889433, 944125141, 921943396, 900327144, 879259927, 858725854, 838709583, 819196296, 800171677, 781621893, 763533573, 745893792, 728690051, 711910261, 695542727, 679576132, 663999525, 648802302, 633974199, 619505272, 605385892, 591606730, 578158742, 565033168, 552221511, 539715536, 527507254, 515588919, 503953014, 492592247, 481499540, 470668023, 460091028, 449762080, 439674890, 429823352, 420201532, 410803667, 401624155, 392657553, 383898571, 375342064, 366983032, 358816611, 350838074, 343042818, 335426371, 327984378, 320712602, 313606922, 306663325, 299877905, 293246861, 286766491, 280433190]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1048).prefactor = (5173987400135099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1048).cutoff/(generalMeanRows 1048).c)).2 =
    (166354556646941/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1048).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1048).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1048).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1048

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1048).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1048).criticalRate j.val*(generalMeanRows 1048).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1048).c*(generalMeanRows 1048).criticalPoint j.val)).2-
      (generalMeanRows 1048).J/2-(generalMeanRows 1048).error (generalMeanGrid j.val)+
      (generalMeanRows 1048).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1048).c)).2-
      (generalMeanRows 1048).J/2-(generalMeanRows 1048).error 4 := by
  have he : (generalMeanRows 1048).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1048) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1048)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1048

/-! Kernel-checked entropy margins for general spectral rectangle 1049. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1049
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5879378530, 5697215392, 5522532444, 5354922215, 5194005727, 5039429987, 4890865755, 4748005546, 4610561843, 4478265487, 4350864231, 4228121425, 4109814835, 3995735568, 3885687088, 3779484330, 3676952886, 3577928255, 3482255168, 3389786959, 3300384988, 3213918118, 3130262220, 3049299727, 2970919218, 2895015032, 2821486911, 2750239672, 2681182897, 2614230650, 2549301210, 2486316827, 2425203489, 2365890709, 2308311324, 2252401308, 2198099597, 2145347926, 2094090676, 2044274729, 1995849334, 1948765982, 1902978288, 1858441874, 1815114274, 1772954827, 1731924589, 1691986246, 1653104030, 1615243643, 1578372185, 1542458082, 1507471026, 1473381911, 1440162774, 1407786745, 1376227989, 1345461664, 1315463871, 1286211609, 1257682740, 1229855940, 1202710674, 1176227149, 1150386290, 1125169703, 1100559647, 1076539005, 1053091260, 1030200462, 1007851213, 986028636, 964718359, 943906490, 923579598, 903724695, 884329220, 865381017, 846868321, 828779744, 811104259, 793831184, 776950172, 760451195, 744324535, 728560769, 713150759, 698085644, 683356824, 668955957, 654874944, 641105924, 627641264, 614473550, 601595580, 589000359, 576681086, 564631154, 552844137, 541313790, 530034038, 518998972, 508202845, 497640063, 487305185, 477192913, 467298090, 457615696, 448140842, 438868767, 429794833, 420914523, 412223433, 403717275, 395391869, 387243138, 379267113, 371459918, 363817780, 356337014, 349014030]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1049).prefactor = (503837096431961/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1049).cutoff/(generalMeanRows 1049).c)).2 =
    (74768549512223/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1049).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1049).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1049).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1049

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1049).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1049).criticalRate j.val*(generalMeanRows 1049).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1049).c*(generalMeanRows 1049).criticalPoint j.val)).2-
      (generalMeanRows 1049).J/2-(generalMeanRows 1049).error (generalMeanGrid j.val)+
      (generalMeanRows 1049).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1049).c)).2-
      (generalMeanRows 1049).J/2-(generalMeanRows 1049).error 4 := by
  have he : (generalMeanRows 1049).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1049) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1049)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1049

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock14 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 14 i) := by
  fin_cases i
  · exact EntropyRow0980.numerical
  · exact EntropyRow0981.numerical
  · exact EntropyRow0982.numerical
  · exact EntropyRow0983.numerical
  · exact EntropyRow0984.numerical
  · exact EntropyRow0985.numerical
  · exact EntropyRow0986.numerical
  · exact EntropyRow0987.numerical
  · exact EntropyRow0988.numerical
  · exact EntropyRow0989.numerical
  · exact EntropyRow0990.numerical
  · exact EntropyRow0991.numerical
  · exact EntropyRow0992.numerical
  · exact EntropyRow0993.numerical
  · exact EntropyRow0994.numerical
  · exact EntropyRow0995.numerical
  · exact EntropyRow0996.numerical
  · exact EntropyRow0997.numerical
  · exact EntropyRow0998.numerical
  · exact EntropyRow0999.numerical
  · exact EntropyRow1000.numerical
  · exact EntropyRow1001.numerical
  · exact EntropyRow1002.numerical
  · exact EntropyRow1003.numerical
  · exact EntropyRow1004.numerical
  · exact EntropyRow1005.numerical
  · exact EntropyRow1006.numerical
  · exact EntropyRow1007.numerical
  · exact EntropyRow1008.numerical
  · exact EntropyRow1009.numerical
  · exact EntropyRow1010.numerical
  · exact EntropyRow1011.numerical
  · exact EntropyRow1012.numerical
  · exact EntropyRow1013.numerical
  · exact EntropyRow1014.numerical
  · exact EntropyRow1015.numerical
  · exact EntropyRow1016.numerical
  · exact EntropyRow1017.numerical
  · exact EntropyRow1018.numerical
  · exact EntropyRow1019.numerical
  · exact EntropyRow1020.numerical
  · exact EntropyRow1021.numerical
  · exact EntropyRow1022.numerical
  · exact EntropyRow1023.numerical
  · exact EntropyRow1024.numerical
  · exact EntropyRow1025.numerical
  · exact EntropyRow1026.numerical
  · exact EntropyRow1027.numerical
  · exact EntropyRow1028.numerical
  · exact EntropyRow1029.numerical
  · exact EntropyRow1030.numerical
  · exact EntropyRow1031.numerical
  · exact EntropyRow1032.numerical
  · exact EntropyRow1033.numerical
  · exact EntropyRow1034.numerical
  · exact EntropyRow1035.numerical
  · exact EntropyRow1036.numerical
  · exact EntropyRow1037.numerical
  · exact EntropyRow1038.numerical
  · exact EntropyRow1039.numerical
  · exact EntropyRow1040.numerical
  · exact EntropyRow1041.numerical
  · exact EntropyRow1042.numerical
  · exact EntropyRow1043.numerical
  · exact EntropyRow1044.numerical
  · exact EntropyRow1045.numerical
  · exact EntropyRow1046.numerical
  · exact EntropyRow1047.numerical
  · exact EntropyRow1048.numerical
  · exact EntropyRow1049.numerical
end SingularValueBounds.KL.Certificates
