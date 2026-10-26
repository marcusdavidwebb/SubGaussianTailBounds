import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 210. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0210
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4880584062, 4702777804, 4533283267, 4371613838, 4217317686, 4069974729, 3929193926, 3794610846, 3665885493, 3542700338, 3424758549, 3311782382, 3203511731, 3099702800, 3000126898, 2904569343, 2812828453, 2724714629, 2640049508, 2558665189, 2480403523, 2405115452, 2332660408, 2262905752, 2195726257, 2131003633, 2068626083, 2008487891, 1950489044, 1894534878, 1840535748, 1788406723, 1738067301, 1689441144, 1642455830, 1597042624, 1553136258, 1510674736, 1469599139, 1429853456, 1391384410, 1354141314, 1318075918, 1283142277, 1249296625, 1216497251, 1184704393, 1153880127, 1123988272, 1094994297, 1066865230, 1039569579, 1013077254, 987359494, 962388796, 938138856, 914584502, 891701639, 869467196, 847859072, 826856090, 806437951, 786585191, 767279139, 748501879, 730236216, 712465638, 695174286, 678346922, 661968902, 646026145, 630505109, 615392765, 600676578, 586344478, 572384842, 558786477, 545538596, 532630802, 520053074, 507795745, 495849491, 484205315, 472854532, 461788758, 450999897, 440480125, 430221886, 420217875, 410461030, 400944521, 391661745, 382606310, 373772033, 365152926, 356743196, 348537230, 340529591, 332715012, 325088390, 317644777, 310379379, 303287544, 296364761, 289606657, 283008985, 276567625, 270278581, 264137969, 258142020, 252287075, 246569577, 240986073, 235533207, 230207717, 225006434, 219926276, 214964247, 210117434, 205383004, 200758200]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 210).prefactor = (1274950120584337/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 210).cutoff/(generalMeanRows 210).c)).2 =
    (47171752694837/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 210).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 210).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 210).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 210

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 210).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 210).criticalRate j.val*(generalMeanRows 210).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 210).c*(generalMeanRows 210).criticalPoint j.val)).2-
      (generalMeanRows 210).J/2-(generalMeanRows 210).error (generalMeanGrid j.val)+
      (generalMeanRows 210).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 210).c)).2-
      (generalMeanRows 210).J/2-(generalMeanRows 210).error 4 := by
  have he : (generalMeanRows 210).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 210) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 210)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0210

/-! Kernel-checked entropy margins for general spectral rectangle 211. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0211
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5104742510, 4929001518, 4761406538, 4601474726, 4448758102, 4302840514, 4163334904, 4029880877, 3902142503, 3779806343, 3662579666, 3550188832, 3442377828, 3338906935, 3239551516, 3144100908, 3052357410, 2964135358, 2879260276, 2797568094, 2718904433, 2643123942, 2570089696, 2499672628, 2431751011, 2366209982, 2302941097, 2241841913, 2182815617, 2125770663, 2070620446, 2017282997, 1965680695, 1915740006, 1867391233, 1820568284, 1775208464, 1731252265, 1688643186, 1647327554, 1607254361, 1568375112, 1530643680, 1494016171, 1458450801, 1423907774, 1390349175, 1357738864, 1326042379, 1295226846, 1265260889, 1236114554, 1207759229, 1180167576, 1153313462, 1127171896, 1101718967, 1076931794, 1052788467, 1029268002, 1006350289, 984016054, 962246811, 941024826, 920333082, 900155238, 880475601, 861279093, 842551220, 824278046, 806446167, 789042683, 772055178, 755471694, 739280715, 723471140, 708032269, 692953786, 678225735, 663838513, 649782847, 636049784, 622630675, 609517165, 596701175, 584174895, 571930772, 559961497, 548259997, 536819425, 525633152, 514694755, 503998011, 493536890, 483305544, 473298306, 463509674, 453934314, 444567049, 435402852, 426436844, 417664284, 409080569, 400681226, 392461909, 384418390, 376546561, 368842428, 361302103, 353921807, 346697859, 339626679, 332704783, 325928776, 319295354, 312801298, 306443474, 300218827, 294124380, 288157233, 282314557]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 211).prefactor = (5050727406408479/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 211).cutoff/(generalMeanRows 211).c)).2 =
    (26290896930817/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 211).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 211).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 211).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 211

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 211).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 211).criticalRate j.val*(generalMeanRows 211).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 211).c*(generalMeanRows 211).criticalPoint j.val)).2-
      (generalMeanRows 211).J/2-(generalMeanRows 211).error (generalMeanGrid j.val)+
      (generalMeanRows 211).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 211).c)).2-
      (generalMeanRows 211).J/2-(generalMeanRows 211).error 4 := by
  have he : (generalMeanRows 211).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 211) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 211)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0211

/-! Kernel-checked entropy margins for general spectral rectangle 212. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0212
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4748913705, 4571241856, 4401947334, 4240539880, 4086564221, 3939597016, 3799244140, 3665138237, 3536936536, 3414318870, 3296985899, 3184657492, 3077071270, 2973981268, 2875156732, 2780381005, 2689450525, 2602173893, 2518371028, 2437872388, 2360518253, 2286158063, 2214649813, 2145859489, 2079660549, 2015933444, 1954565171, 1895448860, 1838483395, 1783573054, 1730627179, 1679559871, 1630289702, 1582739445, 1536835831, 1492509310, 1449693839, 1408326679, 1368348201, 1329701713, 1292333292, 1256191629, 1221227883, 1187395545, 1154650308, 1122949950, 1092254217, 1062524718, 1033724830, 1005819595, 978775641, 952561093, 927145498, 902499750, 878596020, 855407692, 832909302, 811076478, 789885886, 769315178, 749342945, 729948668, 711112677, 692816106, 675040860, 657769573, 640985576, 624672862, 608816058, 593400390, 578411663, 563836225, 549660952, 535873214, 522460862, 509412200, 496715967, 484361318, 472337804, 460635358, 449244276, 438155200, 427359106, 416847291, 406611353, 396643186, 386934962, 377479124, 368268371, 359295650, 350554144, 342037265, 333738643, 325652118, 317771732, 310091719, 302606502, 295310681, 288199029, 281266484, 274508144, 267919261, 261495234, 255231604, 249124049, 243168380, 237360536, 231696575, 226172678, 220785138, 215530357, 210404845, 205405214, 200528176, 195770537, 191129196, 186601143, 182183452, 177873282, 173667871, 169564537]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 212).prefactor = (5133598716496251/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 212).cutoff/(generalMeanRows 212).c)).2 =
    (362222216538093/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 212).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 212).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 212).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 212

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 212).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 212).criticalRate j.val*(generalMeanRows 212).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 212).c*(generalMeanRows 212).criticalPoint j.val)).2-
      (generalMeanRows 212).J/2-(generalMeanRows 212).error (generalMeanGrid j.val)+
      (generalMeanRows 212).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 212).c)).2-
      (generalMeanRows 212).J/2-(generalMeanRows 212).error 4 := by
  have he : (generalMeanRows 212).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 212) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 212)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0212

/-! Kernel-checked entropy margins for general spectral rectangle 213. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0213
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4780386485, 4601537140, 4431120642, 4268643482, 4113647369, 3965706160, 3824423114, 3689428443, 3560377102, 3436946804, 3318836224, 3205763377, 3097464141, 2993690925, 2894211442, 2798807602, 2707274493, 2619419446, 2535061190, 2454029056, 2376162267, 2301309265, 2229327103, 2160080881, 2093443217, 2029293769, 1967518786, 1908010690, 1850667694, 1795393442, 1742096675, 1690690926, 1641094225, 1593228836, 1547021001, 1502400712, 1459301488, 1417660172, 1377416742, 1338514130, 1300898055, 1264516868, 1229321405, 1195264847, 1162302596, 1130392148, 1099492983, 1069566456, 1040575700, 1012485527, 985262343, 958874062, 933290029, 908480944, 884418795, 861076790, 838429295, 816451777, 795120747, 774413710, 754309114, 734786304, 715825479, 697407651, 679514602, 662128852, 645233621, 628812797, 612850903, 597333071, 582245007, 567572973, 553303755, 539424641, 525923401, 512788261, 500007885, 487571357, 475468159, 463688157, 452221581, 441059014, 430191371, 419609889, 409306114, 399271884, 389499321, 379980816, 370709020, 361676833, 352877394, 344304070, 335950450, 327810333, 319877720, 312146810, 304611985, 297267812, 290109028, 283130539, 276327410, 269694860, 263228258, 256923116, 250775085, 244779946, 238933610, 233232113, 227671607, 222248361, 216958755, 211799274, 206766509, 201857149, 197067979, 192395879, 187837817, 183390848, 179052113, 174818831, 170688303]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 213).prefactor = (5167620943855717/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 213).cutoff/(generalMeanRows 213).c)).2 =
    (362222216538093/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 213).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 213).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 213).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 213

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 213).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 213).criticalRate j.val*(generalMeanRows 213).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 213).c*(generalMeanRows 213).criticalPoint j.val)).2-
      (generalMeanRows 213).J/2-(generalMeanRows 213).error (generalMeanGrid j.val)+
      (generalMeanRows 213).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 213).c)).2-
      (generalMeanRows 213).J/2-(generalMeanRows 213).error 4 := by
  have he : (generalMeanRows 213).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 213) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 213)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0213

/-! Kernel-checked entropy margins for general spectral rectangle 214. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0214
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7209300889, 6958985619, 6719180821, 6489332882, 6268926235, 6057479911, 5854544501, 5659699444, 5472550624, 5292728211, 5119884730, 4953693326, 4793846199, 4640053184, 4492040475, 4349549455, 4212335639, 4080167706, 3952826614, 3830104792, 3711805394, 3597741621, 3487736085, 3381620235, 3279233821, 3180424392, 3085046843, 2992962987, 2904041159, 2818155847, 2735187349, 2655021456, 2577549150, 2502666328, 2430273537, 2360275737, 2292582064, 2227105621, 2163763273, 2102475461, 2043166020, 1985762014, 1930193578, 1876393767, 1824298418, 1773846016, 1724977570, 1677636494, 1631768496, 1587321468, 1544245395, 1502492248, 1462015906, 1422772062, 1384718145, 1347813244, 1312018037, 1277294715, 1243606922, 1210919692, 1179199387, 1148413642, 1118531309, 1089522411, 1061358086, 1034010544, 1007453023, 981659747, 956605883, 932267505, 908621553, 885645806, 863318839, 841619997, 820529364, 800027730, 780096567, 760718000, 741874782, 723550271, 705728402, 688393670, 671531106, 655126258, 639165165, 623634350, 608520789, 593811903, 579495537, 565559945, 551993776, 538786057, 525926181, 513403892, 501209273, 489332735, 477765001, 466497098, 455520346, 444826346, 434406969, 424254351, 414360877, 404719176, 395322115, 386162782, 377234488, 368530752, 360045299, 351772049, 343705110, 335838776, 328167515, 320685967, 313388937, 306271388, 299328438, 292555351, 285947539, 279500547, 273210059]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 214).prefactor = (70634056192341/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 214).cutoff/(generalMeanRows 214).c)).2 =
    (4524134975101/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 214).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 214).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 214).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 214

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 214).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 214).criticalRate j.val*(generalMeanRows 214).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 214).c*(generalMeanRows 214).criticalPoint j.val)).2-
      (generalMeanRows 214).J/2-(generalMeanRows 214).error (generalMeanGrid j.val)+
      (generalMeanRows 214).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 214).c)).2-
      (generalMeanRows 214).J/2-(generalMeanRows 214).error 4 := by
  have he : (generalMeanRows 214).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 214) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 214)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0214

/-! Kernel-checked entropy margins for general spectral rectangle 215. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0215
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6790155431, 6593622203, 6405387432, 6224994974, 6052020304, 5886067720, 5726767865, 5573775509, 5426767570, 5285441340, 5149512889, 5018715618, 4892798963, 4771527210, 4654678420, 4542043454, 4433425080, 4328637156, 4227503883, 4129859118, 4035545746, 3944415095, 3856326401, 3771146316, 3688748446, 3609012929, 3531826042, 3457079835, 3384671789, 3314504505, 3246485405, 3180526458, 3116543925, 3054458121, 2994193184, 2935676872, 2878840366, 2823618079, 2769947492, 2717768984, 2667025685, 2617663328, 2569630119, 2522876604, 2477355555, 2433021852, 2389832380, 2347745929, 2306723096, 2266726199, 2227719188, 2189667572, 2152538335, 2116299871, 2080921914, 2046375473, 2012632773, 1979667195, 1947453225, 1915966399, 1885183256, 1855081290, 1825638906, 1796835382, 1768650821, 1741066121, 1714062936, 1687623641, 1661731300, 1636369636, 1611523002, 1587176352, 1563315212, 1539925660, 1516994300, 1494508235, 1472455051, 1450822792, 1429599944, 1408775411, 1388338503, 1368278913, 1348586704, 1329252294, 1310266439, 1291620220, 1273305027, 1255312552, 1237634770, 1220263930, 1203192546, 1186413382, 1169919445, 1153703972, 1137760426, 1122082480, 1106664016, 1091499109, 1076582027, 1061907216, 1047469299, 1033263067, 1019283471, 1005525617, 991984761, 978656302, 965535775, 952618851, 939901325, 927379118, 915048267, 902904924, 890945349, 879165910, 867563075, 856133409, 844873574, 833780322, 822850492, 812081009, 801468877]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 215).prefactor = (18331717773571/3906250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 215).cutoff/(generalMeanRows 215).c)).2 =
    (405172597702031/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 215).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 215).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 215).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 215

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 215).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 215).criticalRate j.val*(generalMeanRows 215).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 215).c*(generalMeanRows 215).criticalPoint j.val)).2-
      (generalMeanRows 215).J/2-(generalMeanRows 215).error (generalMeanGrid j.val)+
      (generalMeanRows 215).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 215).c)).2-
      (generalMeanRows 215).J/2-(generalMeanRows 215).error 4 := by
  have he : (generalMeanRows 215).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 215) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 215)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0215

/-! Kernel-checked entropy margins for general spectral rectangle 216. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0216
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6950525491, 6745702077, 6549533934, 6361546073, 6181296419, 6008372901, 5842390868, 5682990783, 5529836162, 5382611729, 5241021746, 5104788523, 4973651050, 4847363777, 4725695491, 4608428297, 4495356695, 4386286726, 4281035195, 4179428957, 4081304260, 3986506142, 3894887870, 3806310428, 3720642038, 3637757723, 3557538889, 3479872956, 3404652995, 3331777404, 3261149602, 3192677739, 3126274434, 3061856523, 2999344825, 2938663928, 2879741978, 2822510492, 2766904178, 2712860763, 2660320837, 2609227702, 2559527235, 2511167749, 2464099875, 2418276444, 2373652371, 2330184555, 2287831782, 2246554627, 2206315369, 2167077908, 2128807684, 2091471606, 2055037979, 2019476438, 1984757885, 1950854429, 1917739329, 1885386942, 1853772669, 1822872908, 1792665009, 1763127229, 1734238691, 1705979345, 1678329930, 1651271938, 1624787583, 1598859764, 1573472040, 1548608595, 1524254217, 1500394266, 1477014651, 1454101807, 1431642671, 1409624659, 1388035651, 1366863964, 1346098338, 1325727917, 1305742230, 1286131179, 1266885020, 1247994348, 1229450085, 1211243466, 1193366025, 1175809582, 1158566237, 1141628349, 1124988535, 1108639654, 1092574798, 1076787286, 1061270648, 1046018626, 1031025159, 1016284375, 1001790590, 987538291, 973522140, 959736959, 946177727, 932839576, 919717781, 906807759, 894105059, 881605361, 869304470, 857198310, 845282921, 833554456, 822009173, 810643436, 799453706, 788436544, 777588599, 766906615, 756387418]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 216).prefactor = (4891218574344911/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 216).cutoff/(generalMeanRows 216).c)).2 =
    (197586257183723/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 216).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 216).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 216).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 216

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 216).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 216).criticalRate j.val*(generalMeanRows 216).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 216).c*(generalMeanRows 216).criticalPoint j.val)).2-
      (generalMeanRows 216).J/2-(generalMeanRows 216).error (generalMeanGrid j.val)+
      (generalMeanRows 216).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 216).c)).2-
      (generalMeanRows 216).J/2-(generalMeanRows 216).error 4 := by
  have he : (generalMeanRows 216).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 216) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 216)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0216

/-! Kernel-checked entropy margins for general spectral rectangle 217. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0217
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6868341326, 6655349558, 6451398764, 6255994891, 6068678081, 5889019635, 5716619338, 5551103057, 5392120603, 5239343811, 5092464807, 4951194458, 4815260957, 4684408544, 4558396353, 4436997348, 4319997358, 4207194203, 4098396877, 3993424811, 3892107192, 3794282332, 3699797094, 3608506352, 3520272499, 3434964991, 3352459919, 3272639614, 3195392286, 3120611676, 3048196741, 2978051359, 2910084049, 2844207717, 2780339408, 2718400085, 2658314414, 2600010565, 2543420029, 2488477437, 2435120401, 2383289355, 2332927412, 2283980226, 2236395863, 2190124678, 2145119203, 2101334037, 2058725741, 2017252749, 1976875268, 1937555197, 1899256045, 1861942853, 1825582120, 1790141734, 1755590909, 1721900120, 1689041045, 1656986511, 1625710437, 1595187787, 1565394522, 1536307552, 1507904699, 1480164648, 1453066913, 1426591802, 1400720376, 1375434421, 1350716412, 1326549487, 1302917413, 1279804565, 1257195893, 1235076903, 1213433631, 1192252617, 1171520891, 1151225946, 1131355722, 1111898583, 1092843307, 1074179061, 1055895388, 1037982195, 1020429731, 1003228579, 986369641, 969844122, 953643522, 937759624, 922184479, 906910398, 891929942, 877235913, 862821340, 848679477, 834803789, 821187945, 807825811, 794711445, 781839083, 769203139, 756798195, 744618996, 732660442, 720917584, 709385620, 698059885, 686935850, 676009115, 665275408, 654730574, 644370576, 634191490, 624189499, 614360891, 604702056, 595209479, 585879743]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 217).prefactor = (5097896494360983/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 217).cutoff/(generalMeanRows 217).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 217).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 217).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 217).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 217

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 217).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 217).criticalRate j.val*(generalMeanRows 217).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 217).c*(generalMeanRows 217).criticalPoint j.val)).2-
      (generalMeanRows 217).J/2-(generalMeanRows 217).error (generalMeanGrid j.val)+
      (generalMeanRows 217).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 217).c)).2-
      (generalMeanRows 217).J/2-(generalMeanRows 217).error 4 := by
  have he : (generalMeanRows 217).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 217) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 217)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0217

/-! Kernel-checked entropy margins for general spectral rectangle 218. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0218
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6429632449, 6236478017, 6051621124, 5874599071, 5704981408, 5542367105, 5386382029, 5236676694, 5092924250, 4954818667, 4822073111, 4694418472, 4571602024, 4453386226, 4339547614, 4229875802, 4124172566, 4022251005, 3923934776, 3829057385, 3737461539, 3648998553, 3563527791, 3480916163, 3401037651, 3323772872, 3249008675, 3176637764, 3106558347, 3038673815, 2972892434, 2909127067, 2847294908, 2787317236, 2729119185, 2672629529, 2617780482, 2564507505, 2512749132, 2462446803, 2413544709, 2365989643, 2319730865, 2274719968, 2230910762, 2188259155, 2146723045, 2106262218, 2066838256, 2028414439, 1990955665, 1954428366, 1918800435, 1884041148, 1850121104, 1817012152, 1784687334, 1753120829, 1722287895, 1692164817, 1662728862, 1633958228, 1605832002, 1578330118, 1551433317, 1525123109, 1499381740, 1474192154, 1449537964, 1425403420, 1401773380, 1378633284, 1355969126, 1333767430, 1312015225, 1290700024, 1269809804, 1249332983, 1229258399, 1209575297, 1190273308, 1171342432, 1152773024, 1134555776, 1116681707, 1099142144, 1081928712, 1065033323, 1048448160, 1032165669, 1016178546, 1000479729, 985062384, 969919902, 955045885, 940434137, 926078661, 911973646, 898113461, 884492651, 871105924, 857948151, 845014356, 832299710, 819799528, 807509261, 795424492, 783540931, 771854410, 760360878, 749056397, 737937140, 726999383, 716239504, 705653979, 695239378, 684992363, 674909680, 664988165, 655224731, 645616371]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 218).prefactor = (1199401183114559/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 218).cutoff/(generalMeanRows 218).c)).2 =
    (406178128204049/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 218).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 218).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 218).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 218

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 218).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 218).criticalRate j.val*(generalMeanRows 218).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 218).c*(generalMeanRows 218).criticalPoint j.val)).2-
      (generalMeanRows 218).J/2-(generalMeanRows 218).error (generalMeanGrid j.val)+
      (generalMeanRows 218).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 218).c)).2-
      (generalMeanRows 218).J/2-(generalMeanRows 218).error 4 := by
  have he : (generalMeanRows 218).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 218) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 218)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0218

/-! Kernel-checked entropy margins for general spectral rectangle 219. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0219
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6214151988, 6014764294, 5824013039, 5641419233, 5466537186, 5298951595, 5138274930, 4984145117, 4836223455, 4694192747, 4557755618, 4426632991, 4300562716, 4179298320, 4062607870, 3950272938, 3842087659, 3737857863, 3637400284, 3540541832, 3447118925, 3356976869, 3269969293, 3185957622, 3104810589, 3026403790, 2950619260, 2877345089, 2806475064, 2737908327, 2671549068, 2607306234, 2545093252, 2484827782, 2426431474, 2369829751, 2314951595, 2261729359, 2210098579, 2159997807, 2111368446, 2064154600, 2018302935, 1973762541, 1930484807, 1888423307, 1847533681, 1807773535, 1769102342, 1731481343, 1694873466, 1659243235, 1624556699, 1590781349, 1557886054, 1525840992, 1494617587, 1464188449, 1434527318, 1405609009, 1377409363, 1349905198, 1323074265, 1296895202, 1271347495, 1246411437, 1222068094, 1198299268, 1175087463, 1152415856, 1130268264, 1108629116, 1087483429, 1066816777, 1046615270, 1026865530, 1007554668, 988670263, 970200344, 952133365, 934458194, 917164091, 900240692, 883677995, 867466343, 851596410, 836059189, 820845976, 805948360, 791358210, 777067665, 763069120, 749355219, 735918844, 722753105, 709851333, 697207068, 684814053, 672666226, 660757714, 649082822, 637636028, 626411980, 615405483, 604611499, 594025136, 583641648, 573456425, 563464993, 553663002, 544046229, 534610568, 525352029, 516266732, 507350905, 498600879, 490013084, 481584046, 473310385, 465188810, 457216118]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 219).prefactor = (2487803827454453/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 219).cutoff/(generalMeanRows 219).c)).2 =
    (369307592395721/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 219).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 219).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 219).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 219

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 219).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 219).criticalRate j.val*(generalMeanRows 219).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 219).c*(generalMeanRows 219).criticalPoint j.val)).2-
      (generalMeanRows 219).J/2-(generalMeanRows 219).error (generalMeanGrid j.val)+
      (generalMeanRows 219).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 219).c)).2-
      (generalMeanRows 219).J/2-(generalMeanRows 219).error 4 := by
  have he : (generalMeanRows 219).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 219) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 219)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0219

/-! Kernel-checked entropy margins for general spectral rectangle 220. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0220
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5873072747, 5693807957, 5522370182, 5358314830, 5201228585, 5050726672, 4906450419, 4768065081, 4635257885, 4507736274, 4385226324, 4267471308, 4154230401, 4045277504, 3940400164, 3839398604, 3742084821, 3648281774, 3557822629, 3470550070, 3386315669, 3304979294, 3226408577, 3150478412, 3077070496, 3006072899, 2937379674, 2870890482, 2806510260, 2744148896, 2683720935, 2625145308, 2568345069, 2513247161, 2459782187, 2407884205, 2357490528, 2308541547, 2260980551, 2214753572, 2169809233, 2126098604, 2083575073, 2042194217, 2001913686, 1962693094, 1924493913, 1887279376, 1851014384, 1815665421, 1781200472, 1747588942, 1714801590, 1682810453, 1651588787, 1621111002, 1591352608, 1562290155, 1533901187, 1506164188, 1479058541, 1452564479, 1426663050, 1401336071, 1376566094, 1352336374, 1328630831, 1305434018, 1282731098, 1260507808, 1238750435, 1217445794, 1196581196, 1176144434, 1156123754, 1136507839, 1117285786, 1098447091, 1079981627, 1061879632, 1044131688, 1026728710, 1009661931, 992922883, 976503392, 960395560, 944591755, 929084600, 913866961, 898931937, 884272854, 869883249, 855756867, 841887650, 828269728, 814897416, 801765201, 788867737, 776199842, 763756486, 751532788, 739524011, 727725554, 716132950, 704741858, 693548059, 682547453, 671736052, 661109979, 650665460, 640398825, 630306500, 620385008, 610630959, 601041053, 591612077, 582340896, 573224456, 564259779, 555443961, 546774170]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 220).prefactor = (4648543194388167/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 220).cutoff/(generalMeanRows 220).c)).2 =
    (421043266794909/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 220).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 220).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 220).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 220

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 220).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 220).criticalRate j.val*(generalMeanRows 220).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 220).c*(generalMeanRows 220).criticalPoint j.val)).2-
      (generalMeanRows 220).J/2-(generalMeanRows 220).error (generalMeanGrid j.val)+
      (generalMeanRows 220).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 220).c)).2-
      (generalMeanRows 220).J/2-(generalMeanRows 220).error 4 := by
  have he : (generalMeanRows 220).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 220) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 220)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0220

/-! Kernel-checked entropy margins for general spectral rectangle 221. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0221
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5555331432, 5371634644, 5196062260, 5028155754, 4867488737, 4713664151, 4566311758, 4425085911, 4289663540, 4159742353, 4035039205, 3915288630, 3800241505, 3689663845, 3583335695, 3481050132, 3382612342, 3287838781, 3196556408, 3108601974, 3023821370, 2942069031, 2863207380, 2787106318, 2713642752, 2642700154, 2574168159, 2507942186, 2443923088, 2382016826, 2322134169, 2264190406, 2208105087, 2153801777, 2101207822, 2050254138, 2000875011, 1953007905, 1906593288, 1861574468, 1817897435, 1775510718, 1734365246, 1694414223, 1655613005, 1617918986, 1581291492, 1545691683, 1511082452, 1477428343, 1444695460, 1412851393, 1381865142, 1351707041, 1322348701, 1293762937, 1265923715, 1238806094, 1212386170, 1186641030, 1161548700, 1137088105, 1113239021, 1089982037, 1067298518, 1045170566, 1023580987, 1002513259, 981951498, 961880433, 942285375, 923152192, 904467283, 886217555, 868390399, 850973671, 833955669, 817325114, 801071133, 785183240, 769651321, 754465615, 739616703, 725095489, 710893191, 697001324, 683411691, 670116368, 657107694, 644378261, 631920904, 619728689, 607794905, 596113057, 584676853, 573480202, 562517199, 551782126, 541269436, 530973755, 520889867, 511012717, 501337396, 491859143, 482573335, 473475484, 464561230, 455826339, 447266697, 438878306, 430657279, 422599838, 414702309, 406961118, 399372788, 391933936, 384641269, 377491584, 370481759, 363608755, 356869613]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 221).prefactor = (239997004581687/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 221).cutoff/(generalMeanRows 221).c)).2 =
    (377746461041587/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 221).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 221).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 221).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 221

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 221).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 221).criticalRate j.val*(generalMeanRows 221).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 221).c*(generalMeanRows 221).criticalPoint j.val)).2-
      (generalMeanRows 221).J/2-(generalMeanRows 221).error (generalMeanGrid j.val)+
      (generalMeanRows 221).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 221).c)).2-
      (generalMeanRows 221).J/2-(generalMeanRows 221).error 4 := by
  have he : (generalMeanRows 221).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 221) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 221)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0221

/-! Kernel-checked entropy margins for general spectral rectangle 222. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0222
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5414103497, 5237984663, 5069687213, 4908764518, 4754801472, 4607411738, 4466235297, 4330936247, 4201200840, 4076735702, 3957266238, 3842535186, 3732301305, 3626338182, 3524433152, 3426386305, 3332009583, 3241125956, 3153568656, 3069180488, 2987813182, 2909326805, 2833589217, 2760475566, 2689867822, 2621654349, 2555729501, 2491993255, 2430350864, 2370712540, 2312993150, 2257111947, 2202992304, 2150561475, 2099750371, 2050493348, 2002728010, 1956395026, 1911437956, 1867803089, 1825439296, 1784297881, 1744332453, 1705498800, 1667754767, 1631060153, 1595376602, 1560667504, 1526897907, 1494034430, 1462045178, 1430899668, 1400568755, 1371024565, 1342240430, 1314190827, 1286851320, 1260198505, 1234209963, 1208864207, 1184140637, 1160019499, 1136481842, 1113509478, 1091084951, 1069191495, 1047813007, 1026934011, 1006539634, 986615573, 967148070, 948123890, 929530293, 911355012, 893586235, 876212580, 859223080, 842607162, 826354629, 810455646, 794900722, 779680697, 764786727, 750210268, 735943069, 721977153, 708304810, 694918585, 681811266, 668975876, 656405661, 644094084, 632034815, 620221719, 608648855, 597310465, 586200964, 575314938, 564647136, 554192463, 543945974, 533902867, 524058483, 514408293, 504947901, 495673033, 486579536, 477663372, 468920614, 460347444, 451940146, 443695106, 435608806, 427677820, 419898814, 412268540, 404783836, 397441618, 390238883, 383172705, 376240231]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 222).prefactor = (4697060392981179/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 222).cutoff/(generalMeanRows 222).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 222).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 222).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 222).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 222

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 222).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 222).criticalRate j.val*(generalMeanRows 222).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 222).c*(generalMeanRows 222).criticalPoint j.val)).2-
      (generalMeanRows 222).J/2-(generalMeanRows 222).error (generalMeanGrid j.val)+
      (generalMeanRows 222).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 222).c)).2-
      (generalMeanRows 222).J/2-(generalMeanRows 222).error 4 := by
  have he : (generalMeanRows 222).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 222) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 222)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0222

/-! Kernel-checked entropy margins for general spectral rectangle 223. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0223
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5375147676, 5206578311, 5045498269, 4891473771, 4744101942, 4603008104, 4467843378, 4338282520, 4214021996, 4094778230, 3980286039, 3870297208, 3764579200, 3662913984, 3565096970, 3470936029, 3380250610, 3292870921, 3208637181, 3127398937, 3049014427, 2973350004, 2900279598, 2829684216, 2761451490, 2695475250, 2631655132, 2569896212, 2510108671, 2452207476, 2396112091, 2341746204, 2289037473, 2237917290, 2188320560, 2140185494, 2093453419, 2048068596, 2003978053, 1961131426, 1919480811, 1878980629, 1839587494, 1801260090, 1763959060, 1727646897, 1692287843, 1657847794, 1624294215, 1591596050, 1559723650, 1528648692, 1498344115, 1468784052, 1439943766, 1411799597, 1384328900, 1357510000, 1331322138, 1305745425, 1280760803, 1256349999, 1232495487, 1209180452, 1186388756, 1164104904, 1142314012, 1121001778, 1100154458, 1079758833, 1059802190, 1040272292, 1021157365, 1002446066, 984127472, 966191054, 948626665, 931424518, 914575172, 898069518, 881898759, 866054404, 850528248, 835312363, 820399085, 805781003, 791450948, 777401984, 763627395, 750120680, 736875543, 723885881, 711145782, 698649513, 686391514, 674366392, 662568913, 650993998, 639636714, 628492272, 617556017, 606823427, 596290107, 585951783, 575804298, 565843609, 556065782, 546466987, 537043497, 527791680, 518708003, 509789019, 501031373, 492431793, 483987090, 475694154, 467549952, 459551525, 451695987, 443980520, 436402374]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 223).prefactor = (1146626331015131/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 223).cutoff/(generalMeanRows 223).c)).2 =
    (86536649516809/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 223).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 223).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 223).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 223

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 223).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 223).criticalRate j.val*(generalMeanRows 223).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 223).c*(generalMeanRows 223).criticalPoint j.val)).2-
      (generalMeanRows 223).J/2-(generalMeanRows 223).error (generalMeanGrid j.val)+
      (generalMeanRows 223).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 223).c)).2-
      (generalMeanRows 223).J/2-(generalMeanRows 223).error 4 := by
  have he : (generalMeanRows 223).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 223) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 223)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0223

/-! Kernel-checked entropy margins for general spectral rectangle 224. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0224
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4871837865, 4696170598, 4528571102, 4368576551, 4215756774, 4069711408, 3930067357, 3796476523, 3668613765, 3546175059, 3428875848, 3316449538, 3208646141, 3105231042, 3005983872, 2910697483, 2819177011, 2731239020, 2646710709, 2565429196, 2487240848, 2412000669, 2339571737, 2269824681, 2202637195, 2137893596, 2075484409, 2015305978, 1957260115, 1901253765, 1847198697, 1795011217, 1744611902, 1695925348, 1648879935, 1603407612, 1559443693, 1516926666, 1475798010, 1436002037, 1397485727, 1360198584, 1324092500, 1289121624, 1255242239, 1222412650, 1190593075, 1159745547, 1129833813, 1100823252, 1072680785, 1045374797, 1018875063, 993152679, 968179990, 943930533, 920378974, 897501054, 875273536, 853674151, 832681558, 812275293, 792435729, 773144037, 754382145, 736132707, 718379064, 701105215, 684295785, 667935998, 652011647, 636509070, 621415123, 606717161, 592403011, 578460954, 564879703, 551648385, 538756524, 526194021, 513951142, 502018497, 490387029, 479048000, 467992976, 457213814, 446702653, 436451899, 426454214, 416702509, 407189931, 397909855, 388855873, 380021787, 371401602, 362989514, 354779906, 346767341, 338946553, 331312440, 323860063, 316584631, 309481505, 302546185, 295774310, 289161650, 282704100, 276397681, 270238530, 264222898, 258347145, 252607739, 247001249, 241524343, 236173783, 230946426, 225839216, 220849183, 215973441, 211209183, 206553681]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 224).prefactor = (4839574999439711/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 224).cutoff/(generalMeanRows 224).c)).2 =
    (355440903248657/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 224).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 224).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 224).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 224

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 224).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 224).criticalRate j.val*(generalMeanRows 224).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 224).c*(generalMeanRows 224).criticalPoint j.val)).2-
      (generalMeanRows 224).J/2-(generalMeanRows 224).error (generalMeanGrid j.val)+
      (generalMeanRows 224).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 224).c)).2-
      (generalMeanRows 224).J/2-(generalMeanRows 224).error 4 := by
  have he : (generalMeanRows 224).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 224) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 224)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0224

/-! Kernel-checked entropy margins for general spectral rectangle 225. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0225
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5282019979, 5113684368, 4952908105, 4799249576, 4652298788, 4511674604, 4377022283, 4248011268, 4124333207, 4005700168, 3891843023, 3782509995, 3677465331, 3576488102, 3479371107, 3385919871, 3295951739, 3209295032, 3125788284, 3045279538, 2967625696, 2892691925, 2820351103, 2750483315, 2682975382, 2617720425, 2554617465, 2493571048, 2434490898, 2377291598, 2321892287, 2268216384, 2216191330, 2165748342, 2116822192, 2069350993, 2023276007, 1978541457, 1935094356, 1892884352, 1851863569, 1811986472, 1773209735, 1735492115, 1698794337, 1663078985, 1628310401, 1594454587, 1561479117, 1529353051, 1498046854, 1467532324, 1437782520, 1408771694, 1380475232, 1352869591, 1325932247, 1299641641, 1273977129, 1248918936, 1224448114, 1200546498, 1177196668, 1154381911, 1132086188, 1110294099, 1088990854, 1068162240, 1047794598, 1027874793, 1008390190, 989328630, 970678410, 952428257, 934567315, 917085119, 899971580, 883216970, 866811903, 850747319, 835014472, 819604917, 804510492, 789723311, 775235748, 761040430, 747130222, 733498219, 720137737, 707042305, 694205650, 681621697, 669284557, 657188517, 645328039, 633697749, 622292431, 611107022, 600136604, 589376402, 578821775, 568468214, 558311334, 548346872, 538570681, 528978728, 519567086, 510331934, 501269551, 492376315, 483648696, 475083256, 466676643, 458425593, 450326919, 442377519, 434574363, 426914496, 419395038, 412013174, 404766159]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 225).prefactor = (186030736030513/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 225).cutoff/(generalMeanRows 225).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 225).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 225).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 225).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 225

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 225).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 225).criticalRate j.val*(generalMeanRows 225).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 225).c*(generalMeanRows 225).criticalPoint j.val)).2-
      (generalMeanRows 225).J/2-(generalMeanRows 225).error (generalMeanGrid j.val)+
      (generalMeanRows 225).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 225).c)).2-
      (generalMeanRows 225).J/2-(generalMeanRows 225).error 4 := by
  have he : (generalMeanRows 225).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 225) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 225)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0225

/-! Kernel-checked entropy margins for general spectral rectangle 226. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0226
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5356173125, 5185463180, 5022358443, 4866419047, 4717236432, 4574430612, 4437647736, 4306557902, 4180853202, 4060245954, 3944467109, 3833264814, 3726403099, 3623660696, 3524829953, 3429715852, 3338135103, 3249915320, 3164894265, 3082919152, 3003846007, 2927539079, 2853870295, 2782718761, 2713970299, 2647517011, 2583256889, 2521093440, 2460935347, 2402696148, 2346293941, 2291651111, 2238694066, 2187353004, 2137561688, 2089257236, 2042379925, 1996873014, 1952682565, 1909757293, 1868048408, 1827509481, 1788096310, 1749766795, 1712480826, 1676200172, 1640888381, 1606510681, 1573033892, 1540426341, 1508657783, 1477699324, 1447523351, 1418103465, 1389414420, 1361432061, 1334133272, 1307495918, 1281498801, 1256121608, 1231344871, 1207149922, 1183518855, 1160434489, 1137880331, 1115840545, 1094299918, 1073243831, 1052658232, 1032529607, 1012844957, 993591772, 974758009, 956332071, 938302785, 920659387, 903391495, 886489103, 869942553, 853742529, 837880035, 822346386, 807133191, 792232342, 777636002, 763336592, 749326782, 735599478, 722147817, 708965152, 696045046, 683381262, 670967758, 658798675, 646868333, 635171222, 623701996, 612455467, 601426600, 590610503, 580002426, 569597754, 559392003, 549380811, 539559940, 529925268, 520472782, 511198580, 502098864, 493169936, 484408195, 475810134, 467372336, 459091473, 450964300, 442987656, 435158455, 427473692, 419930433, 412525818, 405257054]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 226).prefactor = (581442370523557/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 226).cutoff/(generalMeanRows 226).c)).2 =
    (424452748447531/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 226).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 226).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 226).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 226

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 226).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 226).criticalRate j.val*(generalMeanRows 226).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 226).c*(generalMeanRows 226).criticalPoint j.val)).2-
      (generalMeanRows 226).J/2-(generalMeanRows 226).error (generalMeanGrid j.val)+
      (generalMeanRows 226).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 226).c)).2-
      (generalMeanRows 226).J/2-(generalMeanRows 226).error 4 := by
  have he : (generalMeanRows 226).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 226) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 226)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0226

/-! Kernel-checked entropy margins for general spectral rectangle 227. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0227
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5067428357, 4895730961, 4731782160, 4575135763, 4425377226, 4282120888, 4145007511, 4013702071, 3887891778, 3767284297, 3651606136, 3540601193, 3434029433, 3331665693, 3233298588, 3138729515, 3047771742, 2960249576, 2875997596, 2794859953, 2716689723, 2641348315, 2568704916, 2498635992, 2431024812, 2365761021, 2302740235, 2241863666, 2183037782, 2126173978, 2071188284, 2018001081, 1966536845, 1916723903, 1868494206, 1821783124, 1776529240, 1732674174, 1690162406, 1648941116, 1608960032, 1570171290, 1532529297, 1495990613, 1460513827, 1426059452, 1392589819, 1360068980, 1328462618, 1297737960, 1267863698, 1238809908, 1210547985, 1183050568, 1156291482, 1130245678, 1104889169, 1080198987, 1056153124, 1032730486, 1009910854, 987674832, 966003813, 944879940, 924286069, 904205734, 884623117, 865523017, 846890819, 828712469, 810974447, 793663744, 776767834, 760274660, 744172603, 728450473, 713097480, 698103223, 683457670, 669151142, 655174301, 641518129, 628173919, 615133263, 602388034, 589930379, 577752705, 565847670, 554208172, 542827337, 531698516, 520815267, 510171355, 499760741, 489577570, 479616171, 469871046, 460336863, 451008450, 441880792, 432949020, 424208410, 415654375, 407282460, 399088341, 391067814, 383216795, 375531317, 368007521, 360641656, 353430075, 346369228, 339455664, 332686024, 326057038, 319565525, 313208385, 306982603, 300885240, 294913433, 289064394]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 227).prefactor = (4717494738719263/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 227).cutoff/(generalMeanRows 227).c)).2 =
    (39219188622931/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 227).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 227).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 227).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 227

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 227).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 227).criticalRate j.val*(generalMeanRows 227).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 227).c*(generalMeanRows 227).criticalPoint j.val)).2-
      (generalMeanRows 227).J/2-(generalMeanRows 227).error (generalMeanGrid j.val)+
      (generalMeanRows 227).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 227).c)).2-
      (generalMeanRows 227).J/2-(generalMeanRows 227).error 4 := by
  have he : (generalMeanRows 227).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 227) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 227)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0227

/-! Kernel-checked entropy margins for general spectral rectangle 228. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0228
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5339914537, 5172552061, 5012714144, 4859958305, 4713873874, 4574079210, 4440219223, 4311963150, 4189002558, 4071049552, 3957835142, 3849107781, 3744632031, 3644187350, 3547566986, 3454576976, 3365035222, 3278770648, 3195622430, 3115439282, 3038078807, 2963406894, 2891297164, 2821630459, 2754294367, 2689182786, 2626195520, 2565237899, 2506220435, 2449058495, 2393672001, 2339985150, 2287926151, 2237426988, 2188423187, 2140853606, 2094660241, 2049788038, 2006184724, 1963800641, 1922588602, 1882503744, 1843503396, 1805546961, 1768595793, 1732613090, 1697563796, 1663414497, 1630133339, 1597689937, 1566055298, 1535201748, 1505102858, 1475733378, 1447069178, 1419087185, 1391765333, 1365082504, 1339018484, 1313553916, 1288670254, 1264349723, 1240575283, 1217330586, 1194599948, 1172368311, 1150621217, 1129344774, 1108525631, 1088150953, 1068208392, 1048686069, 1029572548, 1010856817, 992528268, 974576678, 956992190, 939765298, 922886832, 906347940, 890140074, 874254981, 858684683, 843421472, 828457891, 813786730, 799401012, 785293983, 771459102, 757890036, 744580646, 731524983, 718717279, 706151940, 693823538, 681726804, 669856625, 658208034, 646776207, 635556457, 624544227, 613735087, 603124730, 592708964, 582483713, 572445007, 562588983, 552911877, 543410025, 534079856, 524917891, 515920737, 507085088, 498407720, 489885486, 481515318, 473294222, 465219275, 457287624, 449496483, 441843132]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 228).prefactor = (2325067211943427/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 228).cutoff/(generalMeanRows 228).c)).2 =
    (450701753086723/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 228).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 228).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 228).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 228

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 228).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 228).criticalRate j.val*(generalMeanRows 228).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 228).c*(generalMeanRows 228).criticalPoint j.val)).2-
      (generalMeanRows 228).J/2-(generalMeanRows 228).error (generalMeanGrid j.val)+
      (generalMeanRows 228).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 228).c)).2-
      (generalMeanRows 228).J/2-(generalMeanRows 228).error 4 := by
  have he : (generalMeanRows 228).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 228) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 228)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0228

/-! Kernel-checked entropy margins for general spectral rectangle 229. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0229
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5280561976, 5112309789, 4951642697, 4798115327, 4651314297, 4510855418, 4376381203, 4247558630, 4124077134, 4005646804, 3891996745, 3782873602, 3678040223, 3577274437, 3480367947, 3387125315, 3297363041, 3210908710, 3127600222, 3047285071, 2969819694, 2895068866, 2822905140, 2753208334, 2685865058, 2620768270, 2557816869, 2496915321, 2437973305, 2380905388, 2325630722, 2272072765, 2220159014, 2169820765, 2120992885, 2073613595, 2027624278, 1982969289, 1939595782, 1897453552, 1856494879, 1816674387, 1777948912, 1740277377, 1703620677, 1667941563, 1633204548, 1599375804, 1566423073, 1534315582, 1503023964, 1472520179, 1442777448, 1413770184, 1385473926, 1357865287, 1330921891, 1304622324, 1278946087, 1253873543, 1229385880, 1205465063, 1182093799, 1159255501, 1136934248, 1115114757, 1093782349, 1072922921, 1052522916, 1032569302, 1013049540, 993951564, 975263762, 956974947, 939074345, 921551571, 904396614, 887599816, 871151863, 855043762, 839266832, 823812686, 808673224, 793840613, 779307282, 765065907, 751109402, 737430908, 724023785, 710881601, 697998124, 685367317, 672983324, 660840467, 648933239, 637256295, 625804448, 614572660, 603556039, 592749833, 582149423, 571750321, 561548160, 551538696, 541717798, 532081449, 522625737, 513346853, 504241091, 495304837, 486534574, 477926872, 469478390, 461185870, 453046134, 445056085, 437212700, 429513029, 421954195, 414533390, 407247870]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 229).prefactor = (234072065176519/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 229).cutoff/(generalMeanRows 229).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 229).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 229).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 229).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 229

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 229).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 229).criticalRate j.val*(generalMeanRows 229).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 229).c*(generalMeanRows 229).criticalPoint j.val)).2-
      (generalMeanRows 229).J/2-(generalMeanRows 229).error (generalMeanGrid j.val)+
      (generalMeanRows 229).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 229).c)).2-
      (generalMeanRows 229).J/2-(generalMeanRows 229).error 4 := by
  have he : (generalMeanRows 229).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 229) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 229)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0229

/-! Kernel-checked entropy margins for general spectral rectangle 230. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0230
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5318150624, 5148663545, 4986787522, 4832077922, 4684121945, 4542535849, 4406962464, 4277068974, 4152544917, 4033100391, 3918464429, 3808383529, 3702620327, 3600952383, 3503171077, 3409080606, 3318497065, 3231247599, 3147169639, 3066110189, 2987925171, 2912478829, 2839643173, 2769297468, 2701327760, 2635626439, 2572091836, 2510627842, 2451143566, 2393553005, 2337774745, 2283731683, 2231350761, 2180562728, 2131301908, 2083505992, 2037115838, 1992075290, 1948330998, 1905832264, 1864530886, 1824381018, 1785339036, 1747363416, 1710414613, 1674454958, 1639448546, 1605361148, 1572160116, 1539814297, 1508293956, 1477570698, 1447617396, 1418408127, 1389918108, 1362123636, 1335002033, 1308531590, 1282691525, 1257461926, 1232823717, 1208758606, 1185249056, 1162278239, 1139830006, 1117888853, 1096439887, 1075468799, 1054961836, 1034905773, 1015287889, 996095943, 977318149, 958943160, 940960044, 923358264, 906127663, 889258447, 872741163, 856566692, 840726228, 825211267, 810013592, 795125262, 780538600, 766246181, 752240822, 738515573, 725063701, 711878692, 698954231, 686284200, 673862669, 661683889, 649742282, 638032437, 626549103, 615287182, 604241723, 593407918, 582781094, 572356711, 562130355, 552097733, 542254670, 532597105, 523121085, 513822761, 504698389, 495744321, 486957002, 478332972, 469868855, 461561365, 453407294, 445403517, 437546985, 429834723, 422263829, 414831471, 407534884]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 230).prefactor = (4682581089689797/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 230).cutoff/(generalMeanRows 230).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 230).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 230).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 230).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 230

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 230).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 230).criticalRate j.val*(generalMeanRows 230).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 230).c*(generalMeanRows 230).criticalPoint j.val)).2-
      (generalMeanRows 230).J/2-(generalMeanRows 230).error (generalMeanGrid j.val)+
      (generalMeanRows 230).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 230).c)).2-
      (generalMeanRows 230).J/2-(generalMeanRows 230).error 4 := by
  have he : (generalMeanRows 230).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 230) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 230)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0230

/-! Kernel-checked entropy margins for general spectral rectangle 231. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0231
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5260581447, 5090222736, 4927536704, 4772075722, 4623424179, 4481195692, 4345030608, 4214593768, 4089572502, 3969674820, 3854627779, 3744176008, 3638080368, 3536116733, 3438074882, 3343757490, 3252979200, 3165565775, 3081353329, 3000187604, 2921923321, 2846423574, 2773559273, 2703208628, 2635256679, 2569594847, 2506120536, 2444736748, 2385351736, 2327878679, 2272235373, 2218343958, 2166130648, 2115525489, 2066462132, 2018877619, 1972712182, 1927909062, 1884414331, 1842176730, 1801147519, 1761280332, 1722531043, 1684857646, 1648220129, 1612580373, 1577902040, 1544150481, 1511292643, 1479296985, 1448133393, 1417773109, 1388188654, 1359353768, 1331243339, 1303833347, 1277100809, 1251023723, 1225581019, 1200752514, 1176518862, 1152861519, 1129762697, 1107205331, 1085173040, 1063650098, 1042621396, 1022072419, 1001989213, 982358360, 963166952, 944402567, 926053248, 908107480, 890554167, 873382620, 856582530, 840143959, 824057315, 808313345, 792903114, 777817992, 763049644, 748590014, 734431314, 720566013, 706986825, 693686700, 680658814, 667896560, 655393537, 643143543, 631140568, 619378787, 607852548, 596556369, 585484933, 574633077, 563995788, 553568201, 543345586, 533323349, 523497026, 513862276, 504414877, 495150724, 486065824, 477156289, 468418336, 459848283, 451442542, 443197621, 435110116, 427176711, 419394175, 411759357, 404269186, 396920667, 389710877, 382636967, 375696156]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 231).prefactor = (942922277442329/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 231).cutoff/(generalMeanRows 231).c)).2 =
    (107066407213771/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 231).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 231).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 231).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 231

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 231).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 231).criticalRate j.val*(generalMeanRows 231).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 231).c*(generalMeanRows 231).criticalPoint j.val)).2-
      (generalMeanRows 231).J/2-(generalMeanRows 231).error (generalMeanGrid j.val)+
      (generalMeanRows 231).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 231).c)).2-
      (generalMeanRows 231).J/2-(generalMeanRows 231).error 4 := by
  have he : (generalMeanRows 231).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 231) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 231)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0231

/-! Kernel-checked entropy margins for general spectral rectangle 232. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0232
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5316113188, 5146728249, 4984979471, 4830418483, 4682629120, 4541224606, 4405845048, 4276155181, 4151842350, 4032614692, 3918199487, 3808341677, 3702802510, 3601358322, 3503799412, 3409929027, 3319562431, 3232526049, 3148656689, 3067800819, 2989813909, 2914559824, 2841910258, 2771744221, 2703947558, 2638412507, 2575037288, 2513725723, 2454386881, 2396934756, 2341287956, 2287369421, 2235106163, 2184429014, 2135272401, 2087574132, 2041275193, 1996319565, 1952654048, 1910228097, 1868993671, 1828905088, 1789918895, 1751993739, 1715090248, 1679170926, 1644200045, 1610143550, 1576968966, 1544645312, 1513143024, 1482433873, 1452490901, 1423288346, 1394801585, 1367007071, 1339882279, 1313405652, 1287556550, 1262315206, 1237662680, 1213580817, 1190052208, 1167060151, 1144588621, 1122622231, 1101146203, 1080146339, 1059608993, 1039521041, 1019869863, 1000643311, 981829693, 963417750, 945396633, 927755887, 910485435, 893575553, 877016865, 860800317, 844917169, 829358979, 814117590, 799185119, 784553943, 770216688, 756166221, 742395637, 728898251, 715667588, 702697374, 689981530, 677514162, 665289554, 653302161, 641546603, 630017656, 618710250, 607619460, 596740502, 586068726, 575599611, 565328765, 555251912, 545364896, 535663670, 526144298, 516802944, 507635877, 498639461, 489810152, 481144500, 472639138, 464290789, 456096253, 448052411, 440156220, 432404712, 424794988, 417324223, 409989653]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 232).prefactor = (2356479477864383/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 232).cutoff/(generalMeanRows 232).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 232).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 232).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 232).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 232

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 232).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 232).criticalRate j.val*(generalMeanRows 232).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 232).c*(generalMeanRows 232).criticalPoint j.val)).2-
      (generalMeanRows 232).J/2-(generalMeanRows 232).error (generalMeanGrid j.val)+
      (generalMeanRows 232).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 232).c)).2-
      (generalMeanRows 232).J/2-(generalMeanRows 232).error 4 := by
  have he : (generalMeanRows 232).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 232) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 232)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0232

/-! Kernel-checked entropy margins for general spectral rectangle 233. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0233
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5165295887, 4995382448, 4833175537, 4678223837, 4530108389, 4388439767, 4252855552, 4123018079, 3998612400, 3879344460, 3764939443, 3655140284, 3549706307, 3448411998, 3351045882, 3257409500, 3167316471, 3080591638, 2997070283, 2916597403, 2839027049, 2764221713, 2692051767, 2622394941, 2555135842, 2490165510, 2427381008, 2366685038, 2307985584, 2251195588, 2196232641, 2143018699, 2091479818, 2041545904, 1993150490, 1946230512, 1900726116, 1856580466, 1813739570, 1772152115, 1731769318, 1692544777, 1654434337, 1617395969, 1581389646, 1546377235, 1512322389, 1479190457, 1446948385, 1415564630, 1385009084, 1355252993, 1326268886, 1298030510, 1270512761, 1243691631, 1217544145, 1192048312, 1167183074, 1142928256, 1119264526, 1096173348, 1073636947, 1051638266, 1030160936, 1009189238, 988708076, 968702941, 949159889, 930065509, 911406902, 893171654, 875347813, 857923871, 840888741, 824231737, 807942557, 792011268, 776428285, 761184358, 746270556, 731678256, 717399127, 703425115, 689748439, 676361570, 663257228, 650428366, 637868164, 625570019, 613527535, 601734514, 590184950, 578873022, 567793084, 556939658, 546307432, 535891247, 525686098, 515687122, 505889598, 496288937, 486880680, 477660494, 468624164, 459767592, 451086791, 442577883, 434237091, 426060742, 418045258, 410187154, 402483036, 394929599, 387523621, 380261961, 373141558, 366159429, 359312663, 352598422, 346013936]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 233).prefactor = (1186172199875359/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 233).cutoff/(generalMeanRows 233).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 233).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 233).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 233).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 233

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 233).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 233).criticalRate j.val*(generalMeanRows 233).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 233).c*(generalMeanRows 233).criticalPoint j.val)).2-
      (generalMeanRows 233).J/2-(generalMeanRows 233).error (generalMeanGrid j.val)+
      (generalMeanRows 233).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 233).c)).2-
      (generalMeanRows 233).J/2-(generalMeanRows 233).error 4 := by
  have he : (generalMeanRows 233).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 233) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 233)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0233

/-! Kernel-checked entropy margins for general spectral rectangle 234. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0234
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5113803067, 4942983383, 4779906936, 4624123021, 4475213119, 4332788085, 4196485641, 4065968131, 3940920503, 3821048494, 3706076989, 3595748538, 3489822010, 3388071372, 3290284571, 3196262522, 3105818176, 3018775670, 2934969550, 2854244051, 2776452440, 2701456410, 2629125516, 2559336666, 2491973636, 2426926633, 2364091883, 2303371254, 2244671898, 2187905932, 2132990127, 2079845626, 2028397683, 1978575416, 1930311573, 1883542327, 1838207067, 1794248218, 1751611061, 1710243575, 1670096279, 1631122091, 1593276194, 1556515909, 1520800578, 1486091450, 1452351582, 1419545737, 1387640293, 1356603159, 1326403688, 1297012608, 1268401944, 1240544953, 1213416059, 1186990793, 1161245737, 1136158471, 1111707520, 1087872308, 1064633114, 1041971028, 1019867911, 998306360, 977269667, 956741789, 936707316, 917151439, 898059923, 879419077, 861215735, 843437222, 826071341, 809106343, 792530912, 776334143, 760505524, 745034918, 729912545, 715128971, 700675088, 686542101, 672721517, 659205127, 645985000, 633053466, 620403109, 608026754, 595917457, 584068499, 572473370, 561125768, 550019587, 539148909, 528507997, 518091289, 507893391, 497909067, 488133239, 478560977, 469187494, 460008142, 451018405, 442213896, 433590351, 425143625, 416869688, 408764620, 400824611, 393045949, 385425027, 377958329, 370642438, 363474021, 356449835, 349566721, 342821600, 336211473, 329733417, 323384581, 317162186]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 234).prefactor = (4746860781838207/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 234).cutoff/(generalMeanRows 234).c)).2 =
    (1030340617313/2500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 234).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 234).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 234).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 234

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 234).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 234).criticalRate j.val*(generalMeanRows 234).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 234).c*(generalMeanRows 234).criticalPoint j.val)).2-
      (generalMeanRows 234).J/2-(generalMeanRows 234).error (generalMeanGrid j.val)+
      (generalMeanRows 234).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 234).c)).2-
      (generalMeanRows 234).J/2-(generalMeanRows 234).error 4 := by
  have he : (generalMeanRows 234).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 234) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 234)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0234

/-! Kernel-checked entropy margins for general spectral rectangle 235. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0235
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5059900378, 4888325654, 4724555563, 4568136267, 4418646306, 4275693771, 4138913788, 4007966251, 3882533801, 3762319991, 3647047645, 3536457359, 3430306153, 3328366237, 3230423890, 3136278442, 3045741337, 2958635278, 2874793442, 2794058761, 2716283258, 2641327437, 2569059721, 2499355933, 2432098812, 2367177573, 2304487492, 2243929528, 2185409964, 2128840079, 2074135844, 2021217636, 1970009972, 1920441260, 1872443574, 1825952432, 1780906599, 1737247898, 1694921034, 1653873429, 1614055069, 1575418359, 1537917990, 1501510809, 1466155700, 1431813476, 1398446772, 1366019945, 1334498984, 1303851421, 1274046251, 1245053852, 1216845917, 1189395380, 1162676359, 1136664086, 1111334859, 1086665982, 1062635716, 1039223232, 1016408566, 994172571, 972496885, 951363887, 930756662, 910658967, 891055199, 871930367, 853270058, 835060413, 817288100, 799940292, 783004640, 766469253, 750322677, 734553875, 719152211, 704107425, 689409626, 675049266, 661017134, 647304334, 633902276, 620802662, 607997473, 595478956, 583239615, 571272201, 559569699, 548125321, 536932494, 525984856, 515276241, 504800677, 494552377, 484525730, 474715295, 465115796, 455722113, 446529278, 437532469, 428727006, 420108342, 411672061, 403413874, 395329612, 387415222, 379666765, 372080411, 364652434, 357379209, 350257211, 343283008, 336453258, 329764711, 323214200, 316798641, 310515029, 304360439, 298332018, 292426988]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 235).prefactor = (4779330772261187/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 235).cutoff/(generalMeanRows 235).c)).2 =
    (16166723091041/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 235).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 235).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 235).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 235

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 235).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 235).criticalRate j.val*(generalMeanRows 235).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 235).c*(generalMeanRows 235).criticalPoint j.val)).2-
      (generalMeanRows 235).J/2-(generalMeanRows 235).error (generalMeanGrid j.val)+
      (generalMeanRows 235).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 235).c)).2-
      (generalMeanRows 235).J/2-(generalMeanRows 235).error 4 := by
  have he : (generalMeanRows 235).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 235) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 235)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0235

/-! Kernel-checked entropy margins for general spectral rectangle 236. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0236
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5207057093, 5035789092, 4872228505, 4715928449, 4566473888, 4423478847, 4286583935, 4155454121, 4029776747, 3909259720, 3793629904, 3682631644, 3576025440, 3473586738, 3375104828, 3280381840, 3189231828, 3101479927, 3016961582, 2935521844, 2857014713, 2781302544, 2708255488, 2637750989, 2569673303, 2503913067, 2440366895, 2378936995, 2319530829, 2262060786, 2206443878, 2152601464, 2100458986, 2049945727, 2000994582, 1953541849, 1907527030, 1862892643, 1819584052, 1777549305, 1736738979, 1697106042, 1658605718, 1621195360, 1584834336, 1549483915, 1515107170, 1481668872, 1449135406, 1417474683, 1386656056, 1356650248, 1327429280, 1298966399, 1271236022, 1244213667, 1217875906, 1192200305, 1167165375, 1142750525, 1118936021, 1095702937, 1073033119, 1050909146, 1029314297, 1008232512, 987648366, 967547034, 947914265, 928736355, 910000120, 891692872, 873802397, 856316935, 839225153, 822516133, 806179348, 790204647, 774582239, 759302675, 744356834, 729735907, 715431389, 701435058, 687738970, 674335443, 661217048, 648376596, 635807133, 623501925, 611454451, 599658396, 588107641, 576796256, 565718490, 554868769, 544241685, 533831991, 523634594, 513644551, 503857061, 494267463, 484871227, 475663951, 466641358, 457799288, 449133697, 440640650, 432316320, 424156983, 416159013, 408318883, 400633154, 393098482, 385711605, 378469348, 371368616, 364406392, 357579734, 350885777, 344321723]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 236).prefactor = (2358061627831251/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 236).cutoff/(generalMeanRows 236).c)).2 =
    (25885149660141/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 236).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 236).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 236).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 236

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 236).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 236).criticalRate j.val*(generalMeanRows 236).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 236).c*(generalMeanRows 236).criticalPoint j.val)).2-
      (generalMeanRows 236).J/2-(generalMeanRows 236).error (generalMeanGrid j.val)+
      (generalMeanRows 236).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 236).c)).2-
      (generalMeanRows 236).J/2-(generalMeanRows 236).error 4 := by
  have he : (generalMeanRows 236).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 236) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 236)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0236

/-! Kernel-checked entropy margins for general spectral rectangle 237. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0237
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5064237882, 4892571971, 4728684176, 4572124418, 4422474634, 4279345981, 4142376343, 4011228100, 3885586124, 3765155970, 3649662255, 3538847176, 3432469180, 3330301743, 3232132271, 3137761084, 3047000497, 2959673977, 2875615366, 2794668167, 2716684899, 2641526482, 2569061692, 2499166642, 2431724308, 2366624093, 2303761416, 2243037338, 2184358210, 2127635347, 2072784728, 2019726711, 1968385772, 1918690261, 1870572172, 1823966933, 1778813201, 1735052684, 1692629958, 1651492311, 1611589588, 1572874047, 1535300224, 1498824813, 1463406541, 1429006059, 1395585841, 1363110085, 1331544616, 1300856808, 1271015495, 1241990900, 1213754557, 1186279250, 1159538942, 1133508721, 1108164736, 1083484151, 1059445088, 1036026583, 1013208536, 990971677, 969297515, 948168309, 927567026, 907477310, 887883446, 868770337, 850123466, 831928875, 814173135, 796843328, 779927013, 763412216, 747287398, 731541445, 716163641, 701143657, 686471529, 672137643, 658132723, 644447812, 631074261, 618003715, 605228101, 592739615, 580530714, 568594100, 556922715, 545509727, 534348525, 523432707, 512756072, 502312615, 492096513, 482102127, 472323986, 462756785, 453395380, 444234779, 435270135, 426496747, 417910048, 409505603, 401279103, 393226364, 385343317, 377626009, 370070594, 362673336, 355430597, 348338840, 341394624, 334594599, 327935504, 321414165, 315027491, 308772472, 302646174, 296645742, 290768391]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 237).prefactor = (474890508849231/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 237).cutoff/(generalMeanRows 237).c)).2 =
    (398162053215813/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 237).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 237).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 237).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 237

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 237).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 237).criticalRate j.val*(generalMeanRows 237).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 237).c*(generalMeanRows 237).criticalPoint j.val)).2-
      (generalMeanRows 237).J/2-(generalMeanRows 237).error (generalMeanGrid j.val)+
      (generalMeanRows 237).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 237).c)).2-
      (generalMeanRows 237).J/2-(generalMeanRows 237).error 4 := by
  have he : (generalMeanRows 237).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 237) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 237)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0237

/-! Kernel-checked entropy margins for general spectral rectangle 238. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0238
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5016550955, 4844097113, 4679454429, 4522173461, 4371836619, 4228055379, 4090467812, 3958736357, 3832545835, 3711601652, 3595628184, 3484367307, 3377577075, 3275030510, 3176514505, 3081828821, 2990785173, 2903206386, 2818925632, 2737785720, 2659638447, 2584344000, 2511770401, 2441793004, 2374294015, 2309162063, 2246291790, 2185583480, 2126942709, 2070280023, 2015510632, 1962554138, 1911334264, 1861778620, 1813818469, 1767388518, 1722426717, 1678874078, 1636674496, 1595774591, 1556123552, 1517673000, 1480376845, 1444191171, 1409074110, 1374985735, 1341887954, 1309744416, 1278520414, 1248182801, 1218699909, 1190041470, 1162178547, 1135083462, 1108729734, 1083092020, 1058146053, 1033868592, 1010237371, 987231049, 964829164, 943012093, 921761009, 901057843, 880885249, 861226569, 842065797, 823387554, 805177056, 787420084, 770102964, 753212534, 736736129, 720661553, 704977057, 689671325, 674733449, 660152914, 645919580, 632023665, 618455731, 605206667, 592267678, 579630269, 567286235, 555227645, 543446834, 531936391, 520689150, 509698176, 498956760, 488458408, 478196833, 468165945, 458359848, 448772827, 439399343, 430234028, 421271677, 412507241, 403935822, 395552670, 387353171, 379332850, 371487359, 363812478, 356304106, 348958260, 341771067, 334738766, 327857699, 321124309, 314535138, 308086821, 301776085, 295599746, 289554703, 283637940, 277846520, 272177583, 266628344]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 238).prefactor = (2375411252596741/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 238).cutoff/(generalMeanRows 238).c)).2 =
    (96071676680549/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 238).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 238).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 238).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 238

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 238).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 238).criticalRate j.val*(generalMeanRows 238).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 238).c*(generalMeanRows 238).criticalPoint j.val)).2-
      (generalMeanRows 238).J/2-(generalMeanRows 238).error (generalMeanGrid j.val)+
      (generalMeanRows 238).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 238).c)).2-
      (generalMeanRows 238).J/2-(generalMeanRows 238).error 4 := by
  have he : (generalMeanRows 238).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 238) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 238)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0238

/-! Kernel-checked entropy margins for general spectral rectangle 239. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0239
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4966670214, 4793492560, 4628188607, 4470305613, 4319422891, 4175149012, 4037119313, 3904993660, 3778454447, 3657204791, 3540966900, 3429480603, 3322502016, 3219802321, 3121166666, 3026393158, 2935291935, 2847684327, 2763402081, 2682286648, 2604188534, 2528966693, 2456487972, 2386626601, 2319263716, 2254286921, 2191589882, 2131071946, 2072637794, 2016197116, 1961664305, 1908958175, 1858001702, 1808721775, 1761048966, 1714917324, 1670264165, 1627029894, 1585157825, 1544594020, 1505287134, 1467188272, 1430250856, 1394430495, 1359684869, 1325973618, 1293258233, 1261501962, 1230669715, 1200727979, 1171644731, 1143389367, 1115932623, 1089246512, 1063304254, 1038080219, 1013549867, 989689695, 966477183, 943890749, 921909702, 900514196, 879685192, 859404419, 839654336, 820418100, 801679527, 783423068, 765633777, 748297281, 731399756, 714927901, 698868915, 683210472, 667940703, 653048175, 638521869, 624351163, 610525818, 597035957, 583872049, 571024901, 558485634, 546245677, 534296752, 522630859, 511240268, 500117509, 489255356, 478646822, 468285146, 458163787, 448276414, 438616897, 429179300, 419957872, 410947043, 402141413, 393535750, 385124980, 376904182, 368868584, 361013555, 353334601, 345827362, 338487603, 331311213, 324294199, 317432682, 310722893, 304161172, 297743957, 291467789, 285329303, 279325228, 273452382, 267707668, 262088074, 256590669, 251212600, 245951091]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 239).prefactor = (4784385722914539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 239).cutoff/(generalMeanRows 239).c)).2 =
    (37644352926117/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 239).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 239).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 239).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 239

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 239).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 239).criticalRate j.val*(generalMeanRows 239).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 239).c*(generalMeanRows 239).criticalPoint j.val)).2-
      (generalMeanRows 239).J/2-(generalMeanRows 239).error (generalMeanGrid j.val)+
      (generalMeanRows 239).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 239).c)).2-
      (generalMeanRows 239).J/2-(generalMeanRows 239).error 4 := by
  have he : (generalMeanRows 239).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 239) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 239)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0239

/-! Kernel-checked entropy margins for general spectral rectangle 240. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0240
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5012360190, 4839955966, 4675391831, 4518214488, 4368002856, 4224365256, 4086936907, 3955377679, 3829370073, 3708617410, 3592842192, 3481784616, 3375201231, 3272863718, 3174557775, 3080082101, 2989247471, 2901875885, 2817799787, 2736861352, 2658911828, 2583810927, 2511426267, 2441632860, 2374312625, 2309353959, 2246651315, 2186104832, 2127619977, 2071107220, 2016481730, 1963663088, 1912575025, 1863145180, 1815304861, 1768988839, 1724135144, 1680684877, 1638582035, 1597773350, 1558208132, 1519838125, 1482617374, 1446502099, 1411450571, 1377423006, 1344381460, 1312289725, 1281113241, 1250819011, 1221375511, 1192752620, 1164921546, 1137854753, 1111525904, 1085909792, 1060982289, 1036720287, 1013101653, 990105172, 967710511, 945898167, 924649435, 903946361, 883771711, 864108937, 844942140, 826256045, 808035966, 790267782, 772937911, 756033283, 739541318, 723449902, 707747371, 692422484, 677464408, 662862700, 648607289, 634688458, 621096833, 607823364, 594859315, 582196245, 569826002, 557740707, 545932743, 534394746, 523119593, 512100391, 501330473, 490803381, 480512865, 470452870, 460617532, 451001166, 441598264, 432403485, 423411651, 414617736, 406016868, 397604316, 389375490, 381325932, 373451315, 365747433, 358210204, 350835657, 343619937, 336559294, 329650083, 322888758, 316271870, 309796067, 303458083, 297254742, 291182952, 285239703, 279422065, 273727183, 268152278]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 240).prefactor = (2390957394129869/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 240).cutoff/(generalMeanRows 240).c)).2 =
    (3902568737087/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 240).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 240).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 240).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 240

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 240).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 240).criticalRate j.val*(generalMeanRows 240).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 240).c*(generalMeanRows 240).criticalPoint j.val)).2-
      (generalMeanRows 240).J/2-(generalMeanRows 240).error (generalMeanGrid j.val)+
      (generalMeanRows 240).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 240).c)).2-
      (generalMeanRows 240).J/2-(generalMeanRows 240).error 4 := by
  have he : (generalMeanRows 240).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 240) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 240)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0240

/-! Kernel-checked entropy margins for general spectral rectangle 241. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0241
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5079631829, 4907413451, 4743013640, 4585978864, 4435887903, 4292349022, 4154997460, 4023493174, 3897518816, 3776777914, 3660993222, 3549905237, 3443270843, 3340862092, 3242465082, 3147878938, 3056914882, 2969395381, 2885153360, 2804031491, 2725881524, 2650563688, 2577946119, 2507904352, 2440320834, 2375084486, 2312090289, 2251238906, 2192436324, 2135593532, 2080626208, 2027454441, 1976002463, 1926198402, 1877974053, 1831264664, 1786008729, 1742147811, 1699626356, 1658391534, 1618393085, 1579583174, 1541916256, 1505348948, 1469839912, 1435349743, 1401840864, 1369277427, 1337625221, 1306851583, 1276925321, 1247816629, 1219497023, 1191939268, 1165117311, 1139006227, 1113582157, 1088822254, 1064704634, 1041208327, 1018313232, 996000073, 974250360, 953046349, 932371008, 912207980, 892541553, 873356628, 854638692, 836373787, 818548487, 801149873, 784165509, 767583419, 751392068, 735580342, 720137528, 705053295, 690317682, 675921074, 661854196, 648108091, 634674108, 621543894, 608709373, 596162742, 583896453, 571903209, 560175948, 548707838, 537492263, 526522819, 515793302, 505297702, 495030196, 484985136, 475157050, 465540628, 456130721, 446922331, 437910609, 429090845, 420458469, 412009039, 403738242, 395641886, 387715897, 379956316, 372359290, 364921076, 357638031, 350506610, 343523366, 336684941, 329988069, 323429568, 317006339, 310715366, 304553708, 298518502, 292606957]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 241).prefactor = (119515925237469/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 241).cutoff/(generalMeanRows 241).c)).2 =
    (401160556212071/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 241).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 241).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 241).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 241

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 241).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 241).criticalRate j.val*(generalMeanRows 241).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 241).c*(generalMeanRows 241).criticalPoint j.val)).2-
      (generalMeanRows 241).J/2-(generalMeanRows 241).error (generalMeanGrid j.val)+
      (generalMeanRows 241).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 241).c)).2-
      (generalMeanRows 241).J/2-(generalMeanRows 241).error 4 := by
  have he : (generalMeanRows 241).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 241) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 241)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0241

/-! Kernel-checked entropy margins for general spectral rectangle 242. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0242
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5009841042, 4837483998, 4672980382, 4515875016, 4365745120, 4222197483, 4084865941, 3953409120, 3827508403, 3706866108, 3591203838, 3480260985, 3373793383, 3271572076, 3173382196, 3079021944, 2988301656, 2901042946, 2817077923, 2736248473, 2658405593, 2583408784, 2511125485, 2441430558, 2374205804, 2309339520, 2246726087, 2186265589, 2127863457, 2071430141, 2016880803, 1964135031, 1913116576, 1863753102, 1815975956, 1769719953, 1724923173, 1681526775, 1639474818, 1598714099, 1559193998, 1520866332, 1483685220, 1447606958, 1412589895, 1378594328, 1345582390, 1313517953, 1282366539, 1252095227, 1222672574, 1194068538, 1166254401, 1139202707, 1112887191, 1087282721, 1062365241, 1038111714, 1014500075, 991509179, 969118755, 947309368, 926062372, 905359875, 885184703, 865520363, 846351013, 827661428, 809436977, 791663588, 774327726, 757416367, 740916978, 724817487, 709106271, 693772128, 678804265, 664192275, 649926121, 635996122, 622392935, 609107541, 596131233, 583455600, 571072515, 558974127, 547152842, 535601321, 524312461, 513279393, 502495468, 491954249, 481649503, 471575194, 461725472, 452094670, 442677294, 433468017, 424461672, 415653250, 407037887, 398610864, 390367602, 382303654, 374414699, 366696542, 359145108, 351756436, 344526675, 337452082, 330529019, 323753946, 317123420, 310634090, 304282699, 298066073, 291981124, 286024845, 280194310, 274486667, 268899137]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 242).prefactor = (2398545322121211/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 242).cutoff/(generalMeanRows 242).c)).2 =
    (196627688352479/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 242).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 242).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 242).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 242

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 242).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 242).criticalRate j.val*(generalMeanRows 242).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 242).c*(generalMeanRows 242).criticalPoint j.val)).2-
      (generalMeanRows 242).J/2-(generalMeanRows 242).error (generalMeanGrid j.val)+
      (generalMeanRows 242).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 242).c)).2-
      (generalMeanRows 242).J/2-(generalMeanRows 242).error 4 := by
  have he : (generalMeanRows 242).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 242) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 242)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0242

/-! Kernel-checked entropy margins for general spectral rectangle 243. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0243
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5029750512, 4856748134, 4691613046, 4533890378, 4383157588, 4239021639, 4101116485, 3969100813, 3842656025, 3721484413, 3605307514, 3493864624, 3386911450, 3284218878, 3185571864, 3090768408, 2999618629, 2911943908, 2827576109, 2746356859, 2668136890, 2592775427, 2520139630, 2450104075, 2382550274, 2317366234, 2254446044, 2193689496, 2135001728, 2078292902, 2023477888, 1970475992, 1919210681, 1869609339, 1821603039, 1775126324, 1730117010, 1686515992, 1644267075, 1603316805, 1563614316, 1525111185, 1487761297, 1451520720, 1416347581, 1382201959, 1349045775, 1316842698, 1285558048, 1255158712, 1225613058, 1196890861, 1168963227, 1141802526, 1115382329, 1089677343, 1064663354, 1040317176, 1016616596, 993540330, 971067971, 949179950, 927857495, 907082591, 886837946, 867106952, 847873657, 829122730, 810839437, 793009607, 775619610, 758656331, 742107147, 725959903, 710202892, 694824835, 679814863, 665162494, 650857624, 636890502, 623251721, 609932200, 596923172, 584216168, 571803006, 559675781, 547826850, 536248822, 524934550, 513877117, 503069833, 492506217, 482179998, 472085101, 462215639, 452565909, 443130384, 433903704, 424880672, 416056247, 407425538, 398983799, 390726423, 382648938, 374746999, 367016389, 359453009, 352052877, 344812123, 337726983, 330793800, 324009016, 317369172, 310870900, 304510927, 298286063, 292193208, 286229339, 280391517, 274676876, 269082629]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 243).prefactor = (9597011165573/2000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 243).cutoff/(generalMeanRows 243).c)).2 =
    (3902568737087/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 243).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 243).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 243).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 243

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 243).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 243).criticalRate j.val*(generalMeanRows 243).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 243).c*(generalMeanRows 243).criticalPoint j.val)).2-
      (generalMeanRows 243).J/2-(generalMeanRows 243).error (generalMeanGrid j.val)+
      (generalMeanRows 243).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 243).c)).2-
      (generalMeanRows 243).J/2-(generalMeanRows 243).error 4 := by
  have he : (generalMeanRows 243).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 243) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 243)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0243

/-! Kernel-checked entropy margins for general spectral rectangle 244. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0244
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4961496407, 4788386913, 4623179446, 4465417441, 4314676749, 4170562816, 4032708153, 3900770079, 3774428693, 3653385047, 3537359498, 3426090212, 3319331818, 3216854175, 3118441251, 3023890104, 2933009951, 2845621304, 2761555199, 2680652464, 2602763064, 2527745491, 2455466198, 2385799081, 2318625000, 2253831333, 2191311565, 2130964907, 2072695937, 2016414277, 1962034281, 1909474754, 1858658682, 1809512988, 1761968297, 1715958725, 1671421672, 1628297638, 1586530042, 1546065063, 1506851478, 1468840523, 1431985754, 1396242921, 1361569848, 1327926318, 1295273973, 1263576208, 1232798084, 1202906236, 1173868791, 1145655293, 1118236625, 1091584944, 1065673615, 1040477149, 1015971143, 992132230, 968938025, 946367076, 924398817, 903013527, 882192290, 861916950, 842170082, 822934951, 804195484, 785936235, 768142359, 750799580, 733894168, 717412915, 701343105, 685672499, 670389309, 655482180, 640940168, 626752725, 612909680, 599401224, 586217891, 573350547, 560790373, 548528856, 536557769, 524869165, 513455365, 502308942, 491422718, 480789746, 470403308, 460256902, 450344232, 440659203, 431195913, 421948643, 412911852, 404080170, 395448389, 387011462, 378764492, 370702729, 362821564, 355116523, 347583263, 340217570, 333015347, 325972618, 319085518, 312350292, 305763292, 299320969, 293019874, 286856654, 280828045, 274930874, 269162054, 263518579, 257997526, 252596047, 247311370]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 244).prefactor = (2407576969435381/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 244).cutoff/(generalMeanRows 244).c)).2 =
    (15296547849907/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 244).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 244).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 244).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 244

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 244).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 244).criticalRate j.val*(generalMeanRows 244).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 244).c*(generalMeanRows 244).criticalPoint j.val)).2-
      (generalMeanRows 244).J/2-(generalMeanRows 244).error (generalMeanGrid j.val)+
      (generalMeanRows 244).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 244).c)).2-
      (generalMeanRows 244).J/2-(generalMeanRows 244).error 4 := by
  have he : (generalMeanRows 244).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 244) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 244)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0244

/-! Kernel-checked entropy margins for general spectral rectangle 245. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0245
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5032138290, 4859098616, 4693912314, 4536126421, 4385320117, 4241101925, 4103107201, 3970995901, 3844450568, 3723174518, 3606890208, 3495337758, 3388273609, 3285469304, 3186710382, 3091795358, 3000534808, 2912750514, 2828274689, 2746949265, 2668625238, 2593162057, 2520427074, 2450295027, 2382647560, 2317372786, 2254364881, 2193523698, 2134754425, 2077967248, 2023077057, 1970003156, 1918669001, 1869001957, 1820933066, 1774396835, 1729331031, 1685676502, 1643376995, 1602378995, 1562631571, 1524086232, 1486696794, 1450419251, 1415211657, 1381034013, 1347848168, 1315617711, 1284307887, 1253885505, 1224318857, 1195577642, 1167632892, 1140456903, 1114023171, 1088306331, 1063282100, 1038927223, 1015219419, 992137335, 969660502, 947769288, 926444860, 905669142, 885424784, 865695122, 846464150, 827716485, 809437340, 791612496, 774228275, 757271516, 740729551, 724590183, 708841664, 693472676, 678472309, 663830048, 649535751, 635579635, 621952260, 608644516, 595647603, 582953026, 570552576, 558438321, 546602594, 535037980, 523737310, 512693646, 501900276, 491350702, 481038633, 470957975, 461102828, 451467471, 442046362, 432834128, 423825558, 415015598, 406399346, 397972044, 389729074, 381665955, 373778333, 366061981, 358512793, 351126778, 343900059, 336828867, 329909537, 323138506, 316512308, 310027573, 303681020, 297469457, 291389779, 285438961, 279614059, 273912205, 268330609]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 245).prefactor = (37368471035563/7812500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 245).cutoff/(generalMeanRows 245).c)).2 =
    (24204208428771/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 245).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 245).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 245).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 245

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 245).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 245).criticalRate j.val*(generalMeanRows 245).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 245).c*(generalMeanRows 245).criticalPoint j.val)).2-
      (generalMeanRows 245).J/2-(generalMeanRows 245).error (generalMeanGrid j.val)+
      (generalMeanRows 245).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 245).c)).2-
      (generalMeanRows 245).J/2-(generalMeanRows 245).error 4 := by
  have he : (generalMeanRows 245).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 245) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 245)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0245

/-! Kernel-checked entropy margins for general spectral rectangle 246. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0246
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4964223592, 4791072536, 4625809719, 4467980473, 4317162366, 4172962389, 4035014453, 3902977136, 3776531672, 3655380131, 3539243784, 3427861616, 3320988987, 3218396408, 3119868425, 3025202609, 2934208629, 2846707396, 2762530291, 2681518447, 2603522089, 2528399931, 2456018618, 2386252203, 2318981678, 2254094527, 2191484318, 2131050324, 2072697171, 2016334506, 1961876699, 1909242553, 1858355045, 1809141075, 1761531240, 1715459615, 1670863556, 1627683510, 1585862842, 1545347668, 1506086700, 1468031106, 1431134373, 1395352176, 1360642266, 1326964351, 1294279995, 1262552518, 1231746904, 1201829710, 1172768988, 1144534205, 1117096170, 1090426966, 1064499884, 1039289362, 1014770930, 990921149, 967717567, 945138665, 923163814, 901773229, 880947933, 860669711, 840921078, 821685246, 802946085, 784688097, 766896386, 749556627, 732655043, 716178377, 700113873, 684449246, 669172669, 654272745, 639738493, 625559330, 611725049, 598225806, 585052103, 572194777, 559644978, 547394164, 535434082, 523756760, 512354491, 501219828, 490345568, 479724745, 469350618, 459216667, 449316577, 439644236, 430193724, 420959308, 411935431, 403116709, 394497921, 386074006, 377840057, 369791310, 361923148, 354231085, 346710771, 339357980, 332168609, 325138673, 318264301, 311541730, 304967305, 298537473, 292248779, 286097863, 280081458, 274196387, 268439557, 262807961, 257298670, 251908835, 246635681]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 246).prefactor = (4799894002295253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 246).cutoff/(generalMeanRows 246).c)).2 =
    (94856039349827/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 246).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 246).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 246).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 246

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 246).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 246).criticalRate j.val*(generalMeanRows 246).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 246).c*(generalMeanRows 246).criticalPoint j.val)).2-
      (generalMeanRows 246).J/2-(generalMeanRows 246).error (generalMeanGrid j.val)+
      (generalMeanRows 246).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 246).c)).2-
      (generalMeanRows 246).J/2-(generalMeanRows 246).error 4 := by
  have he : (generalMeanRows 246).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 246) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 246)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0246

/-! Kernel-checked entropy margins for general spectral rectangle 247. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0247
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4984183397, 4810395095, 4644508256, 4486068544, 4334653788, 4189871179, 4051354768, 3918763221, 3791777813, 3670100613, 3553452851, 3441573438, 3334217629, 3231155800, 3132172343, 3037064650, 2945642191, 2857725666, 2773146228, 2691744771, 2613371272, 2537884188, 2465149897, 2395042185, 2327441769, 2262235857, 2199317738, 2138586407, 2079946209, 2023306513, 1968581411, 1915689433, 1864553280, 1815099584, 1767258675, 1720964365, 1676153753, 1632767032, 1590747316, 1550040477, 1510594989, 1472361786, 1435294123, 1399347454, 1364479311, 1330649189, 1297818444, 1265950196, 1235009231, 1204961916, 1175776116, 1147421120, 1119867560, 1093087349, 1067053615, 1041740637, 1017123788, 993179481, 969885119, 947219042, 925160486, 903689536, 882787086, 862434801, 842615077, 823311010, 804506362, 786185529, 768333510, 750935883, 733978775, 717448838, 701333225, 685619569, 670295957, 655350916, 640773387, 626552714, 612678619, 599141190, 585930865, 573038416, 560454934, 548171817, 536180758, 524473729, 513042974, 501880995, 490980540, 480334598, 469936386, 459779338, 449857101, 440163523, 430692647, 421438703, 412396100, 403559421, 394923413, 386482986, 378233200, 370169267, 362286540, 354580509, 347046798, 339681158, 332479463, 325437706, 318551994, 311818546, 305233687, 298793844, 292495546, 286335415, 280310169, 274416614, 268651643, 263012233, 257495444, 252098411, 246818349]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 247).prefactor = (4801256145345961/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 247).cutoff/(generalMeanRows 247).c)).2 =
    (37644352926117/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 247).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 247).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 247).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 247

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 247).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 247).criticalRate j.val*(generalMeanRows 247).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 247).c*(generalMeanRows 247).criticalPoint j.val)).2-
      (generalMeanRows 247).J/2-(generalMeanRows 247).error (generalMeanGrid j.val)+
      (generalMeanRows 247).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 247).c)).2-
      (generalMeanRows 247).J/2-(generalMeanRows 247).error 4 := by
  have he : (generalMeanRows 247).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 247) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 247)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0247

/-! Kernel-checked entropy margins for general spectral rectangle 248. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0248
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4917767735, 4743897853, 4577964160, 4419510565, 4268113239, 4123377803, 3984936821, 3852447548, 3725589918, 3604064722, 3487591976, 3375909434, 3268771243, 3165946727, 3067219268, 2972385295, 2881253354, 2793643263, 2709385329, 2628319634, 2550295378, 2475170272, 2402809978, 2333087596, 2265883182, 2201083312, 2138580666, 2078273654, 2020066058, 1963866708, 1909589178, 1857151496, 1806475886, 1757488517, 1710119277, 1664301551, 1619972028, 1577070507, 1535539724, 1495325186, 1456375018, 1418639817, 1382072515, 1346628258, 1312264276, 1278939780, 1246615853, 1215255349, 1184822801, 1155284333, 1126607579, 1098761603, 1071716825, 1045444952, 1019918915, 995112806, 971001818, 947562193, 924771169, 902606930, 881048560, 860076003, 839670016, 819812133, 800484627, 781670477, 763353332, 745517482, 728147824, 711229842, 694749570, 678693576, 663048931, 647803190, 632944371, 618460930, 604341746, 590576102, 577153665, 564064469, 551298904, 538847697, 526701896, 514852861, 503292249, 492011999, 481004324, 470261700, 459776851, 449542742, 439552572, 429799757, 420277930, 410980926, 401902777, 393037705, 384380112, 375924577, 367665843, 359598819, 351718568, 344020301, 336499375, 329151287, 321971666, 314956271, 308100986, 301401813, 294854872, 288456393, 282202716, 276090284, 270115638, 264275421, 258566366, 252985298, 247529129, 242194857, 236979561, 231880399, 226894607]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 248).prefactor = (4818186055278917/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 248).cutoff/(generalMeanRows 248).c)).2 =
    (73732277763823/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 248).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 248).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 248).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 248

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 248).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 248).criticalRate j.val*(generalMeanRows 248).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 248).c*(generalMeanRows 248).criticalPoint j.val)).2-
      (generalMeanRows 248).J/2-(generalMeanRows 248).error (generalMeanGrid j.val)+
      (generalMeanRows 248).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 248).c)).2-
      (generalMeanRows 248).J/2-(generalMeanRows 248).error 4 := by
  have he : (generalMeanRows 248).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 248) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 248)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0248

/-! Kernel-checked entropy margins for general spectral rectangle 249. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0249
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4897704431, 4724476540, 4559171358, 4401332476, 4250535819, 4106386825, 3968517928, 3836586309, 3710271869, 3589275414, 3473317009, 3362134492, 3255482124, 3153129370, 3054859775, 2960469953, 2869768656, 2782575920, 2698722284, 2618048076, 2540402748, 2465644274, 2393638586, 2324259055, 2257386018, 2192906329, 2130712950, 2070704573, 2012785264, 1956864135, 1902855038, 1850676281, 1800250362, 1751503723, 1704366518, 1658772400, 1614658316, 1571964322, 1530633403, 1490611315, 1451846421, 1414289556, 1377893882, 1342614767, 1308409665, 1275237999, 1243061059, 1211841903, 1181545262, 1152137451, 1123586292, 1095861028, 1068932255, 1042771851, 1017352914, 992649693, 968637539, 945292842, 922592987, 900516297, 879041995, 858150154, 837821659, 818038166, 798782069, 780036459, 761785097, 744012378, 726703305, 709843457, 693418969, 677416496, 661823202, 646626726, 631815168, 617377064, 603301370, 589577442, 576195017, 563144200, 550415445, 537999541, 525887599, 514071037, 502541565, 491291180, 480312146, 469596987, 459138476, 448929626, 438963676, 429234089, 419734535, 410458891, 401401225, 392555796, 383917040, 375479568, 367238159, 359187749, 351323430, 343640444, 336134175, 328800143, 321634004, 314631541, 307788659, 301101385, 294565857, 288178329, 281935156, 275832801, 269867825, 264036885, 258336732, 252764207, 247316236, 241989832, 236782087, 231690173, 226711339]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 249).prefactor = (2408341113135531/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 249).cutoff/(generalMeanRows 249).c)).2 =
    (185821008478627/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 249).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 249).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 249).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 249

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 249).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 249).criticalRate j.val*(generalMeanRows 249).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 249).c*(generalMeanRows 249).criticalPoint j.val)).2-
      (generalMeanRows 249).J/2-(generalMeanRows 249).error (generalMeanGrid j.val)+
      (generalMeanRows 249).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 249).c)).2-
      (generalMeanRows 249).J/2-(generalMeanRows 249).error 4 := by
  have he : (generalMeanRows 249).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 249) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 249)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0249

/-! Kernel-checked entropy margins for general spectral rectangle 250. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0250
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4914834760, 4741000982, 4575117624, 4416726682, 4265402595, 4120749422, 3982398311, 3850005245, 3723249004, 3601829350, 3485465366, 3373893974, 3266868577, 3164157830, 3065544525, 2970824564, 2879806028, 2792308324, 2708161400, 2627205023, 2549288121, 2474268170, 2402010633, 2332388439, 2265281506, 2200576290, 2138165382, 2077947119, 2019825230, 1963708510, 1909510509, 1857149250, 1806546960, 1757629824, 1710327751, 1664574162, 1620305784, 1577462462, 1535986983, 1495824912, 1456924434, 1419236208, 1382713236, 1347310729, 1312985990, 1279698302, 1247408819, 1216080470, 1185677863, 1156167195, 1127516174, 1099693937, 1072670978, 1046419075, 1020911232, 996121609, 972025469, 948599121, 925819870, 903665965, 882116553, 861151640, 840752044, 820899356, 801575908, 782764733, 764449534, 746614653, 729245039, 712326223, 695844287, 679785845, 664138011, 648888383, 634025020, 619536417, 605411492, 591639562, 578210331, 565113867, 552340592, 539881262, 527726956, 515869064, 504299267, 493009532, 481992097, 471239461, 460744370, 450499813, 440499006, 430735388, 421202609, 411894521, 402805176, 393928808, 385259837, 376792855, 368522620, 360444052, 352552228, 344842369, 337309846, 329950162, 322758959, 315732004, 308865188, 302154524, 295596138, 289186268, 282921259, 276797560, 270811721, 264960387, 259240297, 253648281, 248181255, 242836221, 237610262, 232500539, 227504290]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 250).prefactor = (4833529169140279/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 250).cutoff/(generalMeanRows 250).c)).2 =
    (185821008478627/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 250).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 250).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 250).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 250

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 250).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 250).criticalRate j.val*(generalMeanRows 250).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 250).c*(generalMeanRows 250).criticalPoint j.val)).2-
      (generalMeanRows 250).J/2-(generalMeanRows 250).error (generalMeanGrid j.val)+
      (generalMeanRows 250).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 250).c)).2-
      (generalMeanRows 250).J/2-(generalMeanRows 250).error 4 := by
  have he : (generalMeanRows 250).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 250) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 250)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0250

/-! Kernel-checked entropy margins for general spectral rectangle 251. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0251
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4852714181, 4678795889, 4512848085, 4354412893, 4203064796, 4058407821, 3920073019, 3787716213, 3661015974, 3539671801, 3423402476, 3311944580, 3205051144, 3102490423, 3004044781, 2909509674, 2818692718, 2731412840, 2647499495, 2566791952, 2489138627, 2414396485, 2342430470, 2273112993, 2206323452, 2141947790, 2079878079, 2020012146, 1962253216, 1906509582, 1852694300, 1800724906, 1750523149, 1702014742, 1655129135, 1609799294, 1565961503, 1523555176, 1482522675, 1442809154, 1404362393, 1367132662, 1331072581, 1296136989, 1262282831, 1229469040, 1197656433, 1166807608, 1136886856, 1107860068, 1079694655, 1052359466, 1025824717, 1000061921, 975043823, 950744336, 927138483, 904202345, 881913004, 860248499, 839187774, 818710638, 798797723, 779430441, 760590954, 742262131, 724427519, 707071310, 690178312, 673733920, 657724089, 642135308, 626954578, 612169387, 597767687, 583737878, 570068783, 556749632, 543770046, 531120017, 518789893, 506770362, 495052442, 483627459, 472487043, 461623109, 451027848, 440693714, 430613416, 420779905, 411186366, 401826206, 392693050, 383780727, 375083266, 366594886, 358309990, 350223158, 342329138, 334622843, 327099341, 319753854, 312581747, 305578528, 298739838, 292061450, 285539261, 279169290, 272947673, 266870660, 260934607, 255135976, 249471332, 243937335, 238530744, 233248404, 228087252, 223044310, 218116682, 213301551, 208596177]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 251).prefactor = (4835175662474757/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 251).cutoff/(generalMeanRows 251).c)).2 =
    (90234835681301/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 251).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 251).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 251).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 251

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 251).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 251).criticalRate j.val*(generalMeanRows 251).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 251).c*(generalMeanRows 251).criticalPoint j.val)).2-
      (generalMeanRows 251).J/2-(generalMeanRows 251).error (generalMeanGrid j.val)+
      (generalMeanRows 251).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 251).c)).2-
      (generalMeanRows 251).J/2-(generalMeanRows 251).error 4 := by
  have he : (generalMeanRows 251).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 251) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 251)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0251

/-! Kernel-checked entropy margins for general spectral rectangle 252. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0252
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4788993170, 4615058309, 4449127781, 4290741894, 4139473419, 3994924762, 3856725441, 3724529822, 3598015098, 3476879456, 3360840432, 3249633422, 3143010324, 3040738317, 2942598737, 2848386058, 2757906961, 2670979477, 2587432206, 2507103596, 2429841282, 2355501478, 2283948410, 2215053803, 2148696397, 2084761501, 2023140585, 1963730897, 1906435104, 1851160970, 1797821039, 1746332358, 1696616207, 1648597851, 1602206307, 1557374129, 1514037205, 1472134570, 1431608225, 1392402971, 1354466258, 1317748036, 1282200619, 1247778555, 1214438507, 1182139142, 1150841019, 1120506493, 1091099622, 1062586072, 1034933041, 1008109175, 982084496, 956830332, 932319252, 908525000, 885422442, 862987505, 841197127, 820029211, 799462571, 779476892, 760052690, 741171269, 722814683, 704965705, 687607789, 670725040, 654302184, 638324540, 622777989, 607648955, 592924376, 578591679, 564638766, 551053983, 537826109, 524944333, 512398234, 500177769, 488273255, 476675352, 465375050, 454363655, 443632775, 433174307, 422980429, 413043584, 403356468, 393912028, 384703441, 375724113, 366967667, 358427933, 350098944, 341974923, 334050279, 326319599, 318777642, 311419332, 304239749, 297234128, 290397851, 283726441, 277215557, 270860989, 264658656, 258604597, 252694969, 246926044, 241294202, 235795929, 230427815, 225186547, 220068907, 215071770, 210192099, 205426944, 200773437, 196228792, 191790298]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 252).prefactor = (4852225177434519/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 252).cutoff/(generalMeanRows 252).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 252).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 252).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 252).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 252

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 252).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 252).criticalRate j.val*(generalMeanRows 252).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 252).c*(generalMeanRows 252).criticalPoint j.val)).2-
      (generalMeanRows 252).J/2-(generalMeanRows 252).error (generalMeanGrid j.val)+
      (generalMeanRows 252).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 252).c)).2-
      (generalMeanRows 252).J/2-(generalMeanRows 252).error 4 := by
  have he : (generalMeanRows 252).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 252) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 252)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0252

/-! Kernel-checked entropy margins for general spectral rectangle 253. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0253
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5200071075, 5029013699, 4865714735, 4709719828, 4560607197, 4417984795, 4281487765, 4150776165, 4025532929, 3905462021, 3790286776, 3679748397, 3573604590, 3471628320, 3373606690, 3279339904, 3188640326, 3101331622, 3017247962, 2936233301, 2858140707, 2782831747, 2710175919, 2640050130, 2572338211, 2506930469, 2443723273, 2382618668, 2323524022, 2266351689, 2211018706, 2157446503, 2105560638, 2055290546, 2006569311, 1959333446, 1913522693, 1869079834, 1825950513, 1784083072, 1743428399, 1703939780, 1665572763, 1628285036, 1592036301, 1556788169, 1522504051, 1489149059, 1456689918, 1425094873, 1394333613, 1364377190, 1335197949, 1306769458, 1279066447, 1252064744, 1225741221, 1200073739, 1175041096, 1150622984, 1126799938, 1103553300, 1080865173, 1058718387, 1037096461, 1015983572, 995364521, 975224702, 955550077, 936327145, 917542920, 899184903, 881241064, 863699816, 846549997, 829780850, 813382005, 797343459, 781655564, 766309007, 751294799, 736604256, 722228993, 708160902, 694392148, 680915152, 667722585, 654807354, 642162591, 629781649, 617658089, 605785672, 594158351, 582770266, 571615732, 560689236, 549985429, 539499117, 529225262, 519158969, 509295483, 499630186, 490158589, 480876328, 471779161, 462862962, 454123718, 445557524, 437160578, 428929182, 420859734, 412948725, 405192740, 397588450, 390132611, 382822062, 375653722, 368624586, 361731724, 354972279, 348343464]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 253).prefactor = (4776632263421303/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 253).cutoff/(generalMeanRows 253).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 253).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 253).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 253).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 253

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 253).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 253).criticalRate j.val*(generalMeanRows 253).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 253).c*(generalMeanRows 253).criticalPoint j.val)).2-
      (generalMeanRows 253).J/2-(generalMeanRows 253).error (generalMeanGrid j.val)+
      (generalMeanRows 253).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 253).c)).2-
      (generalMeanRows 253).J/2-(generalMeanRows 253).error 4 := by
  have he : (generalMeanRows 253).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 253) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 253)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0253

/-! Kernel-checked entropy margins for general spectral rectangle 254. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0254
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5235080385, 5062871371, 4898473002, 4741427864, 4591311338, 4447728735, 4310312743, 4178721132, 4052634699, 3931755418, 3815804759, 3704522185, 3597663767, 3495000946, 3396319388, 3301417954, 3210107744, 3122211236, 3037561486, 2956001397, 2877383047, 2801567072, 2728422091, 2657824182, 2589656395, 2523808297, 2460175560, 2398659571, 2339167072, 2281609829, 2225904318, 2171971442, 2119736257, 2069127723, 2020078474, 1972524595, 1926405423, 1881663354, 1838243665, 1796094354, 1755165974, 1715411499, 1676786178, 1639247412, 1602754634, 1567269195, 1532754260, 1499174707, 1466497036, 1434689278, 1403720919, 1373562815, 1344187126, 1315567241, 1287677721, 1260494230, 1233993485, 1208153196, 1182952022, 1158369516, 1134386082, 1110982937, 1088142063, 1065846174, 1044078679, 1022823649, 1002065780, 981790371, 961983287, 942630937, 923720248, 905238636, 887173991, 869514647, 852249367, 835367323, 818858073, 802711548, 786918034, 771468157, 756352867, 741563421, 727091376, 712928572, 699067120, 685499392, 672218006, 659215823, 646485930, 634021634, 621816452, 609864104, 598158503, 586693748, 575464117, 564464058, 553688188, 543131278, 532788254, 522654190, 512724298, 502993930, 493458565, 484113812, 474955399, 465979172, 457181092, 448557226, 440103748, 431816934, 423693158, 415728889, 407920687, 400265201, 392759166, 385399399, 378182798, 371106339, 364167071, 357362119, 350688675]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 254).prefactor = (961758157135819/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 254).cutoff/(generalMeanRows 254).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 254).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 254).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 254).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 254

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 254).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 254).criticalRate j.val*(generalMeanRows 254).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 254).c*(generalMeanRows 254).criticalPoint j.val)).2-
      (generalMeanRows 254).J/2-(generalMeanRows 254).error (generalMeanGrid j.val)+
      (generalMeanRows 254).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 254).c)).2-
      (generalMeanRows 254).J/2-(generalMeanRows 254).error 4 := by
  have he : (generalMeanRows 254).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 254) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 254)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0254

/-! Kernel-checked entropy margins for general spectral rectangle 255. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0255
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5007048391, 4834753181, 4670323988, 4513303786, 4363268127, 4219822298, 4082598782, 3951254987, 3825471209, 3704948785, 3589408446, 3478588806, 3372245006, 3270147474, 3172080800, 3077842707, 2987243112, 2900103263, 2816254955, 2735539799, 2657808561, 2582920545, 2510743029, 2441150739, 2374025370, 2309255137, 2246734360, 2186363081, 2128046706, 2071695676, 2017225158, 1964554757, 1913608253, 1864313346, 1816601429, 1770407369, 1725669306, 1682328462, 1640328967, 1599617690, 1560144086, 1521860050, 1484719784, 1448679663, 1413698122, 1379735539, 1346754132, 1314717858, 1283592320, 1253344683, 1223943586, 1195359067, 1167562490, 1140526476, 1114224840, 1088632526, 1063725552, 1039480954, 1015876739, 992891829, 970506025, 948699954, 927455036, 906753440, 886578052, 866912439, 847740813, 829048005, 810819437, 793041086, 775699468, 758781606, 742275010, 726167655, 710447958, 695104759, 680127302, 665505218, 651228506, 637287519, 623672947, 610375801, 597387406, 584699378, 572303618, 560192301, 548357858, 536792972, 525490565, 514443789, 503646015, 493090824, 482772004, 472683534, 462819583, 453174498, 443742799, 434519175, 425498472, 416675692, 408045985, 399604642, 391347094, 383268903, 375365759, 367633476, 360067985, 352665334, 345421678, 338333283, 331396514, 324607838, 317963817, 311461106, 305096450, 298866682, 292768716, 286799549, 280956258, 275235992, 269635979]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 255).prefactor = (601502858427977/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 255).cutoff/(generalMeanRows 255).c)).2 =
    (24766431110557/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 255).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 255).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 255).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 255

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 255).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 255).criticalRate j.val*(generalMeanRows 255).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 255).c*(generalMeanRows 255).criticalPoint j.val)).2-
      (generalMeanRows 255).J/2-(generalMeanRows 255).error (generalMeanGrid j.val)+
      (generalMeanRows 255).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 255).c)).2-
      (generalMeanRows 255).J/2-(generalMeanRows 255).error 4 := by
  have he : (generalMeanRows 255).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 255) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 255)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0255

/-! Kernel-checked entropy margins for general spectral rectangle 256. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0256
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5041298145, 4867824382, 4702270443, 4544176175, 4393114226, 4248687183, 4110525015, 3978282789, 3851638610, 3730291777, 3613961106, 3502383425, 3395312201, 3292516290, 3193778810, 3098896100, 3007676775, 2919940863, 2835519007, 2754251734, 2675988791, 2600588518, 2527917285, 2457848962, 2390264435, 2325051154, 2262102716, 2201318478, 2142603201, 2085866712, 2031023599, 1977992917, 1926697923, 1877065824, 1829027542, 1782517501, 1737473415, 1693836107, 1651549323, 1610559568, 1570815952, 1532270042, 1494875725, 1458589079, 1423368253, 1389173356, 1355966345, 1323710933, 1292372487, 1261917947, 1232315737, 1203535691, 1175548977, 1148328029, 1121846482, 1096079108, 1071001762, 1046591324, 1022825649, 999683516, 977144585, 955189354, 933799114, 912955913, 892642519, 872842387, 853539621, 834718949, 816365692, 798465731, 781005491, 763971906, 747352400, 731134866, 715307641, 699859490, 684779583, 670057479, 655683110, 641646762, 627939062, 614550960, 601473720, 588698902, 576218351, 564024188, 552108794, 540464801, 529085083, 517962743, 507091109, 496463717, 486074313, 475916835, 465985411, 456274351, 446778137, 437491420, 428409013, 419525882, 410837145, 402338061, 394024028, 385890580, 377933376, 370148202, 362530961, 355077673, 347784469, 340647587, 333663368, 326828255, 320138787, 313591596, 307183404, 300911022, 294771344, 288761346, 282878085, 277118691, 271480372]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 256).prefactor = (4844938586590937/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 256).cutoff/(generalMeanRows 256).c)).2 =
    (24766431110557/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 256).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 256).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 256).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 256

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 256).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 256).criticalRate j.val*(generalMeanRows 256).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 256).c*(generalMeanRows 256).criticalPoint j.val)).2-
      (generalMeanRows 256).J/2-(generalMeanRows 256).error (generalMeanGrid j.val)+
      (generalMeanRows 256).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 256).c)).2-
      (generalMeanRows 256).J/2-(generalMeanRows 256).error 4 := by
  have he : (generalMeanRows 256).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 256) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 256)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0256

/-! Kernel-checked entropy margins for general spectral rectangle 257. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0257
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5023249772, 4847892915, 4680572231, 4520821140, 4368206289, 4222324658, 4082800967, 3949285364, 3821451339, 3698993855, 3581627653, 3469085722, 3361117910, 3257489666, 3157980886, 3062384867, 2970507348, 2882165635, 2797187792, 2715411907, 2636685408, 2560864440, 2487813286, 2417403835, 2349515090, 2284032709, 2220848585, 2159860457, 2100971538, 2044090187, 1989129588, 1936007460, 1884645785, 1834970553, 1786911528, 1740402023, 1695378695, 1651781355, 1609552783, 1568638561, 1528986917, 1490548573, 1453276608, 1417126328, 1382055144, 1348022456, 1314989546, 1282919477, 1251776997, 1221528451, 1192141695, 1163586017, 1135832065, 1108851771, 1082618292, 1057105942, 1032290135, 1008147330, 984654978, 961791473, 939536104, 917869014, 896771153, 876224244, 856210743, 836713805, 817717250, 799205530, 781163702, 763577399, 746432801, 729716614, 713416042, 697518764, 682012918, 666887073, 652130216, 637731729, 623681374, 609969276, 596585907, 583522071, 570768891, 558317792, 546160492, 534288988, 522695546, 511372686, 500313177, 489510022, 478956451, 468645913, 458572063, 448728760, 439110053, 429710178, 420523547, 411544746, 402768525, 394189790, 385803604, 377605173, 369589846, 361753110, 354090581, 346598004, 339271244, 332106284, 325099223, 318246268, 311543733, 304988032, 298575680, 292303288, 286167558, 280165281, 274293336, 268548683, 262928365, 257429502, 252049290]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 257).prefactor = (4911447026030401/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 257).cutoff/(generalMeanRows 257).c)).2 =
    (77683944061577/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 257).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 257).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 257).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 257

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 257).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 257).criticalRate j.val*(generalMeanRows 257).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 257).c*(generalMeanRows 257).criticalPoint j.val)).2-
      (generalMeanRows 257).J/2-(generalMeanRows 257).error (generalMeanGrid j.val)+
      (generalMeanRows 257).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 257).c)).2-
      (generalMeanRows 257).J/2-(generalMeanRows 257).error 4 := by
  have he : (generalMeanRows 257).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 257) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 257)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0257

/-! Kernel-checked entropy margins for general spectral rectangle 258. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0258
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5027083534, 4854133285, 4689063492, 4531417413, 4380770811, 4236729123, 4098924924, 3967015664, 3840681632, 3719624120, 3603563771, 3492239084, 3385405050, 3282831925, 3184304103, 3089619089, 2998586567, 2911027536, 2826773529, 2745665886, 2667555093, 2592300165, 2519768087, 2449833289, 2382377166, 2317287630, 2254458699, 2193790112, 2135186976, 2078559432, 2023822350, 1970895042, 1919700996, 1870167626, 1822226045, 1775810841, 1730859883, 1687314127, 1645117438, 1604216433, 1564560314, 1526100735, 1488791656, 1452589222, 1417451640, 1383339070, 1350213513, 1318038720, 1286780091, 1256404594, 1226880676, 1198178192, 1170268327, 1143123529, 1116717442, 1091024848, 1066021609, 1041684608, 1017991705, 994921680, 972454195, 950569746, 929249623, 908475874, 888231265, 868499246, 849263919, 830510011, 812222836, 794388275, 776992748, 760023186, 743467010, 727312109, 711546819, 696159901, 681140522, 666478242, 652162988, 638185045, 624535040, 611203921, 598182952, 585463693, 573037990, 560897962, 549035992, 537444713, 526117000, 515045959, 504224919, 493647420, 483307208, 473198226, 463314604, 453650656, 444200867, 434959894, 425922552, 417083814, 408438799, 399982773, 391711140, 383619437, 375703331, 367958611, 360381187, 352967084, 345712441, 338613499, 331666609, 324868218, 318214871, 311703207, 305329956, 299091934, 292986042, 287009264, 281158662, 275431374, 269824614]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 258).prefactor = (4813600907861221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 258).cutoff/(generalMeanRows 258).c)).2 =
    (196627688352479/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 258).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 258).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 258).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 258

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 258).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 258).criticalRate j.val*(generalMeanRows 258).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 258).c*(generalMeanRows 258).criticalPoint j.val)).2-
      (generalMeanRows 258).J/2-(generalMeanRows 258).error (generalMeanGrid j.val)+
      (generalMeanRows 258).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 258).c)).2-
      (generalMeanRows 258).J/2-(generalMeanRows 258).error 4 := by
  have he : (generalMeanRows 258).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 258) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 258)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0258

/-! Kernel-checked entropy margins for general spectral rectangle 259. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0259
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4958495438, 4785442276, 4620304176, 4462622710, 4311972046, 4167956110, 4030206044, 3898377936, 3772150779, 3651224631, 3535318959, 3424171137, 3317535087, 3215180038, 3116889401, 3022459743, 2931699847, 2844429850, 2760480456, 2679692211, 2601914835, 2527006613, 2454833824, 2385270220, 2318196545, 2253500084, 2191074252, 2130818208, 2072636501, 2016438733, 1962139256, 1909656885, 1858914626, 1809839434, 1762361972, 1716416404, 1671940183, 1628873867, 1587160941, 1546747649, 1507582843, 1469617830, 1432806245, 1397103914, 1362468741, 1328860590, 1296241182, 1264573996, 1233824172, 1203958425, 1174944964, 1146753410, 1119354726, 1092721147, 1066826111, 1041644205, 1017151100, 993323500, 970139088, 947576483, 925615184, 904235536, 883418684, 863146535, 843401722, 824167569, 805428058, 787167797, 769371992, 752026418, 735117396, 718631760, 702556844, 686880450, 671590832, 656676675, 642127075, 627931520, 614079875, 600562364, 587369556, 574492346, 561921947, 549649872, 537667924, 525968181, 514542989, 503384945, 492486894, 481841910, 471443296, 461284569, 451359452, 441661868, 432185931, 422925939, 413876365, 405031852, 396387209, 387937399, 379677538, 371602887, 363708847, 355990956, 348444880, 341066411, 333851464, 326796069, 319896369, 313148615, 306549165, 300094478, 293781109, 287605709, 281565021, 275655875, 269875188, 264219958, 258687265, 253274265, 247978188]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 259).prefactor = (4830167995256131/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 259).cutoff/(generalMeanRows 259).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 259).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 259).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 259).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 259

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 259).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 259).criticalRate j.val*(generalMeanRows 259).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 259).c*(generalMeanRows 259).criticalPoint j.val)).2-
      (generalMeanRows 259).J/2-(generalMeanRows 259).error (generalMeanGrid j.val)+
      (generalMeanRows 259).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 259).c)).2-
      (generalMeanRows 259).J/2-(generalMeanRows 259).error 4 := by
  have he : (generalMeanRows 259).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 259) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 259)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0259

/-! Kernel-checked entropy margins for general spectral rectangle 260. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0260
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4894645766, 4721463829, 4556218252, 4398450743, 4247735520, 4103676479, 3965904666, 3834076008, 3707869280, 3586984275, 3471140148, 3360073923, 3253539137, 3151304606, 3053153301, 2958881328, 2868296987, 2781219921, 2697480324, 2616918224, 2539382816, 2464731851, 2392831073, 2323553698, 2256779930, 2192396521, 2130296351, 2070378049, 2012545639, 1956708203, 1902779583, 1850678085, 1800326221, 1751650453, 1704580968, 1659051457, 1614998912, 1572363441, 1531088088, 1491118667, 1452403611, 1414893818, 1378542524, 1343305171, 1309139283, 1276004362, 1243861774, 1212674653, 1182407807, 1153027629, 1124502015, 1096800285, 1069893111, 1043752446, 1018351457, 993664469, 969666901, 946335214, 923646859, 901580228, 880114605, 859230127, 838907742, 819129164, 799876845, 781133933, 762884243, 745112223, 727802926, 710941982, 694515571, 678510397, 662913666, 647713061, 632896722, 618453227, 604371568, 590641137, 577251709, 564193420, 551456757, 539032541, 526911911, 515086314, 503547489, 492287456, 481298506, 470573185, 460104290, 449884855, 439908139, 430167625, 420657002, 411370163, 402301195, 393444371, 384794143, 376345137, 368092143, 360030112, 352154148, 344459504, 336941573, 329595889, 322418115, 315404042, 308549586, 301850780, 295303772, 288904818, 282650285, 276536639, 270560447, 264718372, 259007169, 253423684, 247964847, 242627674, 237409262, 232306786, 227317496]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 260).prefactor = (2415930028110817/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 260).cutoff/(generalMeanRows 260).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 260).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 260).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 260).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 260

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 260).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 260).criticalRate j.val*(generalMeanRows 260).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 260).c*(generalMeanRows 260).criticalPoint j.val)).2-
      (generalMeanRows 260).J/2-(generalMeanRows 260).error (generalMeanGrid j.val)+
      (generalMeanRows 260).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 260).c)).2-
      (generalMeanRows 260).J/2-(generalMeanRows 260).error 4 := by
  have he : (generalMeanRows 260).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 260) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 260)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0260

/-! Kernel-checked entropy margins for general spectral rectangle 261. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0261
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4911627680, 4737844890, 4572025996, 4413711114, 4262472986, 4117914134, 3979664324, 3847378288, 3720733687, 3599429272, 3483183226, 3371731658, 3264827251, 3162238019, 3063746179, 2969147130, 2878248508, 2790869329, 2706839199, 2625997590, 2548193174, 2473283208, 2401132971, 2331615238, 2264609800, 2200003014, 2137687388, 2077561200, 2019528141, 1963496979, 1909381253, 1857098990, 1806572431, 1757727783, 1710494991, 1664807515, 1620602131, 1577818736, 1536400179, 1496292085, 1457442707, 1419802775, 1383325361, 1347965751, 1313681326, 1280431444, 1248177338, 1216882013, 1186510156, 1157028044, 1128403461, 1100605620, 1073605092, 1047373732, 1021884615, 997111976, 973031149, 949618513, 926851441, 904708249, 883168151, 862211216, 841818322, 821971123, 802652008, 783844068, 765531060, 747697380, 730328029, 713408586, 696925184, 680864480, 665213636, 649960293, 635092550, 620598943, 606468427, 592690360, 579254477, 566150882, 553370029, 540902707, 528740025, 516873399, 505294541, 493995441, 482968365, 472205833, 461700617, 451445725, 441434395, 431660086, 422116466, 412797407, 403696974, 394809421, 386129182, 377650862, 369369234, 361279232, 353375943, 345654602, 338110588, 330739418, 323536740, 316498333, 309620095, 302898048, 296328324, 289907170, 283630937, 277496080, 271499153, 265636809, 259905792, 254302934, 248825158, 243469468, 238232951, 233112771, 228106171]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 261).prefactor = (38788993081929/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 261).cutoff/(generalMeanRows 261).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 261).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 261).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 261).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 261

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 261).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 261).criticalRate j.val*(generalMeanRows 261).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 261).c*(generalMeanRows 261).criticalPoint j.val)).2-
      (generalMeanRows 261).J/2-(generalMeanRows 261).error (generalMeanGrid j.val)+
      (generalMeanRows 261).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 261).c)).2-
      (generalMeanRows 261).J/2-(generalMeanRows 261).error 4 := by
  have he : (generalMeanRows 261).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 261) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 261)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0261

/-! Kernel-checked entropy margins for general spectral rectangle 262. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0262
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4975561213, 4801912449, 4636205989, 4477981827, 4326812665, 4182301066, 4044076902, 3911795079, 3785133482, 3663791139, 3547486552, 3435956190, 3328953128, 3226245801, 3127616875, 3032862216, 2941789950, 2854219594, 2769981269, 2688914973, 2610869909, 2535703873, 2463282685, 2393479662, 2326175138, 2261256010, 2198615325, 2138151897, 2079769944, 2023378759, 1968892398, 1916229397, 1865312498, 1816068402, 1768427536, 1722323836, 1677694540, 1634480002, 1592623511, 1552071128, 1512771527, 1474675850, 1437737569, 1401912360, 1367157982, 1333434162, 1300702487, 1268926311, 1238070654, 1208102118, 1178988801, 1150700219, 1123207237, 1096481992, 1070497833, 1045229257, 1020651853, 996742245, 973478040, 950837780, 928800896, 907347665, 886459167, 866117247, 846304478, 827004127, 808200119, 789877011, 772019958, 754614686, 737647467, 721105093, 704974851, 689244503, 673902263, 658936775, 644337099, 630092687, 616193369, 602629334, 589391120, 576469590, 563855927, 551541615, 539518429, 527778419, 516313904, 505117458, 494181898, 483500277, 473065874, 462872183, 452912907, 443181947, 433673396, 424381533, 415300813, 406425860, 397751465, 389272573, 380984284, 372881842, 364960633, 357216179, 349644131, 342240268, 335000489, 327920811, 320997364, 314226386, 307604223, 301127320, 294792223, 288595569, 282534090, 276604607, 270804024, 265129331, 259577595, 254145965, 248831660]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 262).prefactor = (2423396050999463/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 262).cutoff/(generalMeanRows 262).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 262).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 262).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 262).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 262

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 262).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 262).criticalRate j.val*(generalMeanRows 262).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 262).c*(generalMeanRows 262).criticalPoint j.val)).2-
      (generalMeanRows 262).J/2-(generalMeanRows 262).error (generalMeanGrid j.val)+
      (generalMeanRows 262).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 262).c)).2-
      (generalMeanRows 262).J/2-(generalMeanRows 262).error 4 := by
  have he : (generalMeanRows 262).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 262) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 262)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0262

/-! Kernel-checked entropy margins for general spectral rectangle 263. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0263
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4992685723, 4818439308, 4652162532, 4493393806, 4341704362, 4196695393, 4057995500, 3925258399, 3798160868, 3676400898, 3559696023, 3447781805, 3340410467, 3237349650, 3138381270, 3043300492, 2951914780, 2864043031, 2779514781, 2698169477, 2619855803, 2544431067, 2471760625, 2401717360, 2334181192, 2269038629, 2206182353, 2145510827, 2086927939, 2030342671, 1975668783, 1922824531, 1871732389, 1822318809, 1774513976, 1728251600, 1683468702, 1640105431, 1598104882, 1557412929, 1517978070, 1479751277, 1442685865, 1406737356, 1371863363, 1338023474, 1305179146, 1273293606, 1242331752, 1212260073, 1183046555, 1154660612, 1127073007, 1100255780, 1074182191, 1048826648, 1024164656, 1000172757, 976828483, 954110301, 931997573, 910470506, 889510115, 869098184, 849217225, 829850447, 810981721, 792595550, 774677038, 757211862, 740186246, 723586938, 707401180, 691616693, 676221649, 661204654, 646554730, 632261293, 618314136, 604703419, 591419641, 578453639, 565796564, 553439869, 541375302, 529594887, 518090914, 506855933, 495882736, 485164352, 474694037, 464465262, 454471708, 444707257, 435165981, 425842138, 416730164, 407824666, 399120416, 390612342, 382295526, 374165198, 366216727, 358445618, 350847510, 343418165, 336153468, 329049424, 322102148, 315307867, 308662912, 302163718, 295806816, 289588835, 283506495, 277556604, 271736057, 266041833, 260470990, 255020665, 249688070]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 263).prefactor = (607934178041811/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 263).cutoff/(generalMeanRows 263).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 263).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 263).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 263).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 263

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 263).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 263).criticalRate j.val*(generalMeanRows 263).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 263).c*(generalMeanRows 263).criticalPoint j.val)).2-
      (generalMeanRows 263).J/2-(generalMeanRows 263).error (generalMeanGrid j.val)+
      (generalMeanRows 263).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 263).c)).2-
      (generalMeanRows 263).J/2-(generalMeanRows 263).error 4 := by
  have he : (generalMeanRows 263).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 263) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 263)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0263

/-! Kernel-checked entropy margins for general spectral rectangle 264. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0264
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4928668511, 4754282784, 4587888583, 4429024430, 4277261583, 4132201187, 3993471720, 3860726719, 3733642727, 3611917448, 3495268087, 3383429840, 3276154529, 3173209365, 3074375809, 2979448550, 2888234556, 2800552216, 2716230545, 2635108456, 2557034098, 2481864233, 2409463672, 2339704749, 2272466836, 2207635897, 2145104068, 2084769273, 2026534869, 1970309307, 1916005828, 1863542172, 1812840311, 1763826198, 1716429532, 1670583544, 1626224790, 1583292959, 1541730701, 1501483452, 1462499287, 1424728763, 1388124791, 1352642502, 1318239127, 1284873885, 1252507873, 1221103970, 1190626739, 1161042339, 1132318443, 1104424158, 1077329952, 1051007582, 1025430031, 1000571444, 976407068, 952913203, 930067141, 907847123, 886232292, 865202647, 844739000, 824822941, 805436799, 786563605, 768187061, 750291507, 732861893, 715883748, 699343157, 683226731, 667521587, 652215322, 637295995, 622752103, 608572562, 594746691, 581264193, 568115135, 555289940, 542779363, 530574482, 518666685, 507047654, 495709353, 484644018, 473844145, 463302481, 453012010, 442965946, 433157726, 423580994, 414229602, 405097596, 396179208, 387468852, 378961117, 370650756, 362532686, 354601976, 346853846, 339283659, 331886914, 324659247, 317596420, 310694318, 303948949, 297356432, 290912999, 284614991, 278458849, 272441116, 266558433, 260807531, 255185235, 249688454, 244314182, 239059497, 233921553, 228897582]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 264).prefactor = (4865446377026529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 264).cutoff/(generalMeanRows 264).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 264).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 264).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 264).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 264

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 264).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 264).criticalRate j.val*(generalMeanRows 264).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 264).c*(generalMeanRows 264).criticalPoint j.val)).2-
      (generalMeanRows 264).J/2-(generalMeanRows 264).error (generalMeanGrid j.val)+
      (generalMeanRows 264).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 264).c)).2-
      (generalMeanRows 264).J/2-(generalMeanRows 264).error 4 := by
  have he : (generalMeanRows 264).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 264) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 264)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0264

/-! Kernel-checked entropy margins for general spectral rectangle 265. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0265
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4945768466, 4770777710, 4603806206, 4444390876, 4292101490, 4146537808, 4007327021, 3874121463, 3746596554, 3624448951, 3507394877, 3395168608, 3287521107, 3184218775, 3085042318, 2989785710, 2898255250, 2810268698, 2725654473, 2644250933, 2565905697, 2490475031, 2417823277, 2347822326, 2280351132, 2215295263, 2152546480, 2092002355, 2033565907, 1977145271, 1922653387, 1870007709, 1819129939, 1769945771, 1722384664, 1676379613, 1631866957, 1588786175, 1547079716, 1506692831, 1467573410, 1429671842, 1392940873, 1357335478, 1322812742, 1289331739, 1256853434, 1225340576, 1194757604, 1165070561, 1136247008, 1108255944, 1081067735, 1054654040, 1028987748, 1004042914, 979794701, 956219323, 933293997, 910996888, 889307065, 868204457, 847669812, 827684655, 808231252, 789292578, 770852277, 752894634, 735404548, 718367498, 701769520, 685597178, 669837545, 654478175, 639507086, 624912734, 610683997, 596810158, 583280882, 570086204, 557216512, 544662529, 532415304, 520466193, 508806849, 497429210, 486325484, 475488142, 464909903, 454583730, 444502811, 434660561, 425050603, 415666767, 406503077, 397553746, 388813170, 380275917, 371936724, 363790489, 355832263, 348057251, 340460799, 333038392, 325785648, 318698317, 311772269, 305003496, 298388106, 291922319, 285602459, 279424958, 273386348, 267483254, 261712400, 256070597, 250554745, 245161827, 239888911, 234733141, 229691740]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 265).prefactor = (4882326983372843/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 265).cutoff/(generalMeanRows 265).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 265).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 265).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 265).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 265

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 265).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 265).criticalRate j.val*(generalMeanRows 265).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 265).c*(generalMeanRows 265).criticalPoint j.val)).2-
      (generalMeanRows 265).J/2-(generalMeanRows 265).error (generalMeanGrid j.val)+
      (generalMeanRows 265).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 265).c)).2-
      (generalMeanRows 265).J/2-(generalMeanRows 265).error 4 := by
  have he : (generalMeanRows 265).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 265) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 265)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0265

/-! Kernel-checked entropy margins for general spectral rectangle 266. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0266
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4849452847, 4675575255, 4509682241, 4351314025, 4200043372, 4055472751, 3917231809, 3784975099, 3658380049, 3537145131, 3420988204, 3309645020, 3202867870, 3100424347, 3002096226, 2907678440, 2816978145, 2729813859, 2646014682, 2565419568, 2487876667, 2413242708, 2341382439, 2272168104, 2205478960, 2141200836, 2079225714, 2019451351, 1961780918, 1906122674, 1852389656, 1800499391, 1750373634, 1701938114, 1655122304, 1609859204, 1566085139, 1523739568, 1482764907, 1443106365, 1404711784, 1367531497, 1331518190, 1296626773, 1262814262, 1230039660, 1198263858, 1167449530, 1137561038, 1108564350, 1080426948, 1053117757, 1026607065, 1000866458, 975868751, 951587927, 927999080, 905078357, 882802908, 861150834, 840101145, 819633712, 799729225, 780369158, 761535727, 743211858, 725381151, 708027852, 691136817, 674693492, 658683878, 643094510, 627912434, 613125178, 598720738, 584687551, 571014479, 557690789, 544706136, 532050547, 519714400, 507688417, 495963643, 484531435, 473383448, 462511624, 451908179, 441565592, 431476593, 421634155, 412031483, 402662006, 393519365, 384597409, 375890183, 367391923, 359097047, 351000148, 343095990, 335379497, 327845751, 320489985, 313307576, 306294040, 299445030, 292756328, 286223839, 279843591, 273611728, 267524505, 261578286, 255769541, 250094839, 244550846, 239134325, 233842129, 228671196, 223618553, 218681308, 213856648, 209141836]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 266).prefactor = (9700870072559/2000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 266).cutoff/(generalMeanRows 266).c)).2 =
    (181959985431671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 266).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 266).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 266).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 266

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 266).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 266).criticalRate j.val*(generalMeanRows 266).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 266).c*(generalMeanRows 266).criticalPoint j.val)).2-
      (generalMeanRows 266).J/2-(generalMeanRows 266).error (generalMeanGrid j.val)+
      (generalMeanRows 266).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 266).c)).2-
      (generalMeanRows 266).J/2-(generalMeanRows 266).error 4 := by
  have he : (generalMeanRows 266).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 266) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 266)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0266

/-! Kernel-checked entropy margins for general spectral rectangle 267. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0267
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4921815321, 4747702718, 4581561214, 4422931063, 4271385110, 4126525950, 3987983394, 3855412196, 3728490014, 3606915577, 3490407025, 3378700413, 3271548351, 3168718766, 3069993783, 2975168693, 2884051019, 2796459655, 2712224078, 2631183628, 2553186839, 2478090827, 2405760727, 2336069168, 2268895793, 2204126810, 2141654580, 2081377231, 2023198304, 1967026420, 1912774974, 1860361844, 1809709129, 1760742896, 1713392947, 1667592608, 1623278517, 1580390442, 1538871099, 1498665987, 1459723235, 1421993450, 1385429588, 1349986819, 1315622408, 1282295605, 1249967537, 1218601105, 1188160893, 1158613081, 1129925356, 1102066842, 1075008017, 1048720650, 1023177732, 998353415, 974222956, 950762656, 927949815, 905762677, 884180387, 863182945, 842751168, 822866646, 803511707, 784669386, 766323382, 748458038, 731058302, 714109704, 697598328, 681510784, 665834190, 650556143, 635664700, 621148358, 606996034, 593197046, 579741096, 566618253, 553818937, 541333906, 529154239, 517271321, 505676836, 494362749, 483321298, 472544979, 462026538, 451758963, 441735468, 431949490, 422394678, 413064883, 403954153, 395056722, 386367007, 377879598, 369589251, 361490885, 353579570, 345850530, 338299130, 330920872, 323711394, 316666460, 309781961, 303053903, 296478412, 290051722, 283770175, 277630217, 271628395, 265761350, 260025819, 254418628, 248936690, 243577004, 238336649, 233212783, 228202642]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 267).prefactor = (303095762784639/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 267).cutoff/(generalMeanRows 267).c)).2 =
    (93283917303509/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 267).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 267).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 267).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 267

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 267).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 267).criticalRate j.val*(generalMeanRows 267).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 267).c*(generalMeanRows 267).criticalPoint j.val)).2-
      (generalMeanRows 267).J/2-(generalMeanRows 267).error (generalMeanGrid j.val)+
      (generalMeanRows 267).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 267).c)).2-
      (generalMeanRows 267).J/2-(generalMeanRows 267).error 4 := by
  have he : (generalMeanRows 267).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 267) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 267)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0267

/-! Kernel-checked entropy margins for general spectral rectangle 268. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0268
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4847720963, 4673869288, 4508008953, 4349679240, 4198452065, 4053929130, 3915739389, 3783536773, 3656998149, 3535821483, 3419724183, 3308441595, 3201725649, 3099343616, 3001076985, 2906720436, 2816080899, 2728976699, 2645236762, 2564699895, 2487214118, 2412636050, 2340830346, 2271669171, 2205031720, 2140803769, 2078877259, 2019149916, 1961524891, 1905910429, 1852219560, 1800369814, 1750282949, 1701884706, 1655104575, 1609875576, 1566134056, 1523819500, 1482874354, 1443243856, 1404875882, 1367720799, 1331731330, 1296862420, 1263071122, 1230316478, 1198559417, 1167762651, 1137890583, 1108909216, 1080786073, 1053490116, 1026991672, 1001262362, 976275040, 952003724, 928423543, 905510680, 883242318, 861596592, 840552544, 820090076, 800189910, 780833549, 762003240, 743681935, 725853263, 708501495, 691611514, 675168790, 659159348, 643569748, 628387055, 613598822, 599193063, 585158237, 571483224, 558157310, 545170168, 532511841, 520172724, 508143554, 496415392, 484979609, 473827875, 462952143, 452344642, 441997862, 431904547, 422057680, 412450477, 403076375, 393929026, 385002287, 376290212, 367787045, 359487212, 351385313, 343476119, 335754561, 328215726, 320854854, 313667326, 306648666, 299794530, 293100704, 286563099, 280177746, 273940793, 267848499, 261897232, 256083463, 250403765, 244854808, 239433357, 234136265, 228960476, 223903016, 218960997, 214131605, 209412108]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 268).prefactor = (2428985777495039/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 268).cutoff/(generalMeanRows 268).c)).2 =
    (91353405780031/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 268).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 268).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 268).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 268

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 268).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 268).criticalRate j.val*(generalMeanRows 268).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 268).c*(generalMeanRows 268).criticalPoint j.val)).2-
      (generalMeanRows 268).J/2-(generalMeanRows 268).error (generalMeanGrid j.val)+
      (generalMeanRows 268).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 268).c)).2-
      (generalMeanRows 268).J/2-(generalMeanRows 268).error 4 := by
  have he : (generalMeanRows 268).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 268) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 268)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0268

/-! Kernel-checked entropy margins for general spectral rectangle 269. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0269
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4857926226, 4683744820, 4517561943, 4358917013, 4207382047, 4062558820, 3924076331, 3791588530, 3664772283, 3543325533, 3426965647, 3315427915, 3208464195, 3105841673, 3007341745, 2912758984, 2821900210, 2734583623, 2650638025, 2569902089, 2492223698, 2417459332, 2345473503, 2276138230, 2209332561, 2144942125, 2082858715, 2022979909, 1965208709, 1909453215, 1855626309, 1803645378, 1753432037, 1704911885, 1658014275, 1612672087, 1568821536, 1526401976, 1485355721, 1445627884, 1407166216, 1369920965, 1333844732, 1298892351, 1265020759, 1232188891, 1200357567, 1169489397, 1139548682, 1110501328, 1082314762, 1054957854, 1028400840, 1002615257, 977573872, 953250623, 929620559, 906659787, 884345416, 862655510, 841569042, 821065846, 801126580, 781732685, 762866347, 744510461, 726648599, 709264978, 692344430, 675872374, 659834786, 644218180, 629009576, 614196483, 599766874, 585709167, 572012204, 558665234, 545657893, 532980191, 520622489, 508575493, 496830233, 485378049, 474210584, 463319764, 452697792, 442337133, 432230505, 422370870, 412751419, 403365571, 394206956, 385269411, 376546971, 368033862, 359724492, 351613446, 343695477, 335965501, 328418591, 321049972, 313855013, 306829223, 299968246, 293267857, 286723954, 280332558, 274089806, 267991947, 262035338, 256216444, 250531826, 244978146, 239552161, 234250718, 229070750, 224009279, 219063407, 214230316, 209507267]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 269).prefactor = (2429455065413449/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 269).cutoff/(generalMeanRows 269).c)).2 =
    (181959985431671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 269).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 269).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 269).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 269

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 269).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 269).criticalRate j.val*(generalMeanRows 269).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 269).c*(generalMeanRows 269).criticalPoint j.val)).2-
      (generalMeanRows 269).J/2-(generalMeanRows 269).error (generalMeanGrid j.val)+
      (generalMeanRows 269).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 269).c)).2-
      (generalMeanRows 269).J/2-(generalMeanRows 269).error 4 := by
  have he : (generalMeanRows 269).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 269) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 269)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0269

/-! Kernel-checked entropy margins for general spectral rectangle 270. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0270
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4866414410, 4691928659, 4525455413, 4366533285, 4214733544, 4069657270, 3930932812, 3798213518, 3671175687, 3549516734, 3432953534, 3321220914, 3214070297, 3111268465, 3012596429, 2917848406, 2826830875, 2739361721, 2655269446, 2574392441, 2496578324, 2421683324, 2349571714, 2280115293, 2213192896, 2148689951, 2086498064, 2026514632, 1968642490, 1912789574, 1858868618, 1806796861, 1756495783, 1707890853, 1660911299, 1615489886, 1571562716, 1529069036, 1487951061, 1448153808, 1409624937, 1372314608, 1336175340, 1301161886, 1267231111, 1234341876, 1202454935, 1171532829, 1141539799, 1112441691, 1084205875, 1056801167, 1030197750, 1004367112, 979281972, 954916224, 931244872, 908243981, 885890620, 864162816, 843039503, 822500482, 802526377, 783098596, 764199293, 745811333, 727918262, 710504267, 693554154, 677053316, 660987706, 645343813, 630108635, 615269659, 600814838, 586732568, 573011673, 559641382, 546611314, 533911459, 521532165, 509464120, 497698337, 486226143, 475039165, 464129316, 453488784, 443110022, 432985735, 423108872, 413472614, 404070366, 394895748, 385942586, 377204906, 368676922, 360353033, 352227815, 344296011, 336552528, 328992432, 321610938, 314403408, 307365341, 300492376, 293780279, 287224942, 280822379, 274568719, 268460205, 262493189, 256664127, 250969576, 245406193, 239970727, 234660020, 229471002, 224400687, 219446173, 214604638, 209873336]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 270).prefactor = (2433700016891831/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 270).cutoff/(generalMeanRows 270).c)).2 =
    (181959985431671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 270).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 270).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 270).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 270

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 270).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 270).criticalRate j.val*(generalMeanRows 270).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 270).c*(generalMeanRows 270).criticalPoint j.val)).2-
      (generalMeanRows 270).J/2-(generalMeanRows 270).error (generalMeanGrid j.val)+
      (generalMeanRows 270).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 270).c)).2-
      (generalMeanRows 270).J/2-(generalMeanRows 270).error 4 := by
  have he : (generalMeanRows 270).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 270) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 270)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0270

/-! Kernel-checked entropy margins for general spectral rectangle 271. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0271
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4859628230, 4685423338, 4519210069, 4360528786, 4208952360, 4064083342, 3925551426, 3793011193, 3666140075, 3544636523, 3428218364, 3316621297, 3209597545, 3106914623, 3008354215, 2913711155, 2822792487, 2735416614, 2651412511, 2570619005, 2492884112, 2418064424, 2346024548, 2276636587, 2209779655, 2145339434, 2083207763, 2023282250, 1965465924, 1909666897, 1855798063, 1803776807, 1753524741, 1704967457, 1658034290, 1612658105, 1568775094, 1526324586, 1485248868, 1445493023, 1407004772, 1369734328, 1333634259, 1298659361, 1264766537, 1231914684, 1200064584, 1169178810, 1139221625, 1110158896, 1081958014, 1054587810, 1028018484, 1002221535, 977169694, 952836864, 929198060, 906229352, 883907817, 862211485, 841119297, 820611057, 800667392, 781269712, 762400175, 744041648, 726177675, 708792447, 691870771, 675398041, 659360209, 643743765, 628535708, 613723525, 599295169, 585239037, 571543953, 558199146, 545194236, 532519215, 520164428, 508120565, 496378641, 484929982, 473766217, 462879260, 452261299, 441904789, 431802436, 421947190, 412332235, 402950975, 393797034, 384864239, 376146617, 367638386, 359333945, 351227872, 343314914, 335589979, 328048136, 320684603, 313494742, 306474058, 299618190, 292922908, 286384106, 279997802, 273760126, 267667326, 261715756, 255901875, 250222244, 244673521, 239252459, 233955904, 228780787, 223724128, 218783026, 213954663, 209236296]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 271).prefactor = (4851332677664933/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 271).cutoff/(generalMeanRows 271).c)).2 =
    (5662946035573/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 271).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 271).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 271).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 271

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 271).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 271).criticalRate j.val*(generalMeanRows 271).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 271).c*(generalMeanRows 271).criticalPoint j.val)).2-
      (generalMeanRows 271).J/2-(generalMeanRows 271).error (generalMeanGrid j.val)+
      (generalMeanRows 271).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 271).c)).2-
      (generalMeanRows 271).J/2-(generalMeanRows 271).error 4 := by
  have he : (generalMeanRows 271).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 271) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 271)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0271

/-! Kernel-checked entropy margins for general spectral rectangle 272. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0272
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4868153856, 4693643343, 4527138473, 4368178803, 4216336455, 4071213282, 3932438329, 3799665570, 3672571872, 3550855157, 3434232756, 3322439905, 3215228393, 3112365327, 3013632007, 2918822907, 2827744733, 2740215569, 2656064092, 2575128844, 2497257574, 2422306624, 2350140363, 2280630669, 2213656445, 2149103171, 2086862497, 2026831853, 1968914095, 1913017175, 1859053835, 1806941314, 1756601087, 1707958615, 1660943110, 1615487318, 1571527319, 1529002336, 1487854556, 1448028965, 1409473191, 1372137360, 1335973958, 1300937701, 1266985416, 1234075928, 1202169952, 1171229992, 1141220250, 1112106535, 1083856178, 1056437956, 1029822017, 1003979810, 978884019, 954508501, 930828225, 907819221, 885458526, 863724130, 842594939, 822050719, 802072066, 782640355, 763737714, 745346978, 727451665, 710035938, 693084575, 676582944, 660516976, 644873135, 629638397, 614800228, 600346559, 586265768, 572546657, 559178439, 546150713, 533453455, 521076993, 509012001, 497249477, 485780733, 474597382, 463691325, 453054736, 442680057, 432559981, 422687445, 413055621, 403657904, 394487903, 385539437, 376806521, 368283362, 359964353, 351844059, 343917218, 336178731, 328623657, 321247205, 314044730, 307011729, 300143834, 293436806, 286886532, 280489024, 274240405, 268136916, 262174905, 256350824, 250661228, 245102771, 239672198, 234366351, 229182155, 224116624, 219166854, 214330021, 209603376]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 272).prefactor = (2429921875372291/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 272).cutoff/(generalMeanRows 272).c)).2 =
    (5662946035573/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 272).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 272).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 272).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 272

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 272).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 272).criticalRate j.val*(generalMeanRows 272).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 272).c*(generalMeanRows 272).criticalPoint j.val)).2-
      (generalMeanRows 272).J/2-(generalMeanRows 272).error (generalMeanGrid j.val)+
      (generalMeanRows 272).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 272).c)).2-
      (generalMeanRows 272).J/2-(generalMeanRows 272).error 4 := by
  have he : (generalMeanRows 272).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 272) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 272)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0272

/-! Kernel-checked entropy margins for general spectral rectangle 273. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0273
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4797429075, 4623187823, 4456965006, 4298300119, 4146765182, 4001961900, 3863519137, 3731090654, 3604353071, 3483004047, 3366760618, 3255357714, 3148546798, 3046094637, 2947782182, 2853403546, 2762765068, 2675684460, 2591990018, 2511519908, 2434121495, 2359650739, 2287971629, 2218955663, 2152481367, 2088433848, 2026704386, 1967190047, 1909793327, 1854421826, 1800987935, 1749408556, 1699604830, 1651501888, 1605028624, 1560117473, 1516704211, 1474727764, 1434130030, 1394855716, 1356852177, 1320069275, 1284459240, 1249976541, 1216577764, 1184221503, 1152868248, 1122480287, 1093021615, 1064457838, 1036756095, 1009884978, 983814456, 958515807, 933961550, 910125384, 886982131, 864507674, 842678913, 821473708, 800870840, 780849956, 761391538, 742476857, 724087935, 706207516, 688819024, 671906535, 655454750, 639448961, 623875025, 608719341, 593968823, 579610880, 565633388, 552024675, 538773500, 525869032, 513300833, 501058842, 489133358, 477515025, 466194818, 455164025, 444414242, 433937352, 423725518, 413771168, 404066989, 394605911, 385381103, 376385958, 367614087, 359059311, 350715650, 342577318, 334638715, 326894417, 319339175, 311967903, 304775673, 297757712, 290909393, 284226231, 277703877, 271338116, 265124858, 259060134, 253140096, 247361009, 241719246, 236211288, 230833718, 225583217, 220456563, 215450623, 210562357, 205788808, 201127104, 196574453, 192128141]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 273).prefactor = (2430386233155157/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 273).cutoff/(generalMeanRows 273).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 273).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 273).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 273).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 273

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 273).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 273).criticalRate j.val*(generalMeanRows 273).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 273).c*(generalMeanRows 273).criticalPoint j.val)).2-
      (generalMeanRows 273).J/2-(generalMeanRows 273).error (generalMeanGrid j.val)+
      (generalMeanRows 273).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 273).c)).2-
      (generalMeanRows 273).J/2-(generalMeanRows 273).error 4 := by
  have he : (generalMeanRows 273).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 273) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 273)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0273

/-! Kernel-checked entropy margins for general spectral rectangle 274. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0274
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4805879839, 4631331659, 4464816036, 4305871658, 4154069789, 4009011433, 3870324801, 3737663042, 3610702209, 3489139426, 3372691232, 3261092090, 3154093024, 3051460391, 2952974757, 2858429871, 2767631732, 2680397730, 2596555859, 2515943999, 2438409247, 2363807310, 2292001936, 2222864397, 2156273005, 2092112665, 2030274466, 1970655290, 1913157465, 1857688426, 1804160411, 1752490174, 1702598717, 1654411041, 1607855913, 1562865651, 1519375915, 1477325526, 1436656278, 1397312781, 1359242298, 1322394603, 1286721840, 1252178399, 1218720790, 1186307532, 1154899047, 1124457558, 1094946994, 1066332901, 1038582361, 1011663910, 985547465, 960204251, 935606741, 911728588, 888544567, 866030521, 844163308, 822920750, 802281589, 782225438, 762732744, 743784744, 725363430, 707451514, 690032392, 673090112, 656609347, 640575363, 624973993, 609791612, 595015111, 580631875, 566629762, 552997078, 539722560, 526795361, 514205022, 501941467, 489994976, 478356177, 467016029, 455965806, 445197087, 434701741, 424471918, 414500034, 404778760, 395301017, 386059960, 377048969, 368261647, 359691801, 351333442, 343180775, 335228187, 327470248, 319901697, 312517440, 305312541, 298282218, 291421835, 284726901, 278193058, 271816084, 265591880, 259516473, 253586007, 247796740, 242145039, 236627379, 231240336, 225980587, 220844901, 215830143, 210933266, 206151309, 201481393, 196920723, 192466578]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 274).prefactor = (97386696228029/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 274).cutoff/(generalMeanRows 274).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 274).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 274).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 274).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 274

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 274).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 274).criticalRate j.val*(generalMeanRows 274).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 274).c*(generalMeanRows 274).criticalPoint j.val)).2-
      (generalMeanRows 274).J/2-(generalMeanRows 274).error (generalMeanGrid j.val)+
      (generalMeanRows 274).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 274).c)).2-
      (generalMeanRows 274).J/2-(generalMeanRows 274).error 4 := by
  have he : (generalMeanRows 274).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 274) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 274)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0274

/-! Kernel-checked entropy margins for general spectral rectangle 275. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0275
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4795634109, 4621414984, 4455221315, 4296591651, 4145097153, 4000338749, 3861944603, 3729567842, 3602884519, 3481591775, 3365406190, 3254062278, 3147311132, 3044919190, 2946667109, 2852348740, 2761770192, 2674748972, 2591113200, 2510700884, 2433359254, 2358944156, 2287319477, 2218356633, 2151934078, 2087936864, 2026256224, 1966789188, 1909438228, 1854110925, 1800719660, 1749181330, 1699417078, 1651352044, 1604915134, 1560038799, 1516658834, 1474714189, 1434146788, 1394901365, 1356925307, 1320168506, 1284583227, 1250123971, 1216747361, 1184412026, 1153078494, 1122709089, 1093267841, 1064720396, 1037033929, 1010177068, 984119819, 958833495, 934290652, 910465023, 887331465, 864865895, 843045245, 821847410, 801251200, 781236294, 761783205, 742873231, 724488426, 706611559, 689226081, 672316097, 655866330, 639862097, 624289280, 609134301, 594384095, 580026092, 566048190, 552438737, 539186509, 526280695, 513710873, 501467001, 489539393, 477918709, 466595938, 455562385, 444809656, 434329650, 424114541, 414156770, 404449035, 394984278, 385755676, 376756634, 367980772, 359421920, 351074106, 342931554, 334988669, 327240038, 319680415, 312304723, 305108040, 298085599, 291232778, 284545098, 278018215, 271647919, 265430122, 259360863, 253436296, 247652689, 242006420, 236493973, 231111933, 225856985, 220725909, 215715575, 210822944, 206045063, 201379061, 196822148, 192371612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 275).prefactor = (4868369755466683/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 275).cutoff/(generalMeanRows 275).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 275).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 275).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 275).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 275

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 275).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 275).criticalRate j.val*(generalMeanRows 275).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 275).c*(generalMeanRows 275).criticalPoint j.val)).2-
      (generalMeanRows 275).J/2-(generalMeanRows 275).error (generalMeanGrid j.val)+
      (generalMeanRows 275).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 275).c)).2-
      (generalMeanRows 275).J/2-(generalMeanRows 275).error 4 := by
  have he : (generalMeanRows 275).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 275) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 275)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0275

/-! Kernel-checked entropy margins for general spectral rectangle 276. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0276
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4804047466, 4629522695, 4463037459, 4304129499, 4152369221, 4007356857, 3868719915, 3736110915, 3609205341, 3487699805, 3371310386, 3259771134, 3152832707, 3050261131, 2951836678, 2857352839, 2766615382, 2679441494, 2595658993, 2515105603, 2437628287, 2363082636, 2291332301, 2222248469, 2155709384, 2091599895, 2029811044, 1970239681, 1912788106, 1857363737, 1803878803, 1752250055, 1702398498, 1654249140, 1607730762, 1562775697, 1519319628, 1477301396, 1436662824, 1397348550, 1359305867, 1322484581, 1286836872, 1252317161, 1218881996, 1186489933, 1155101430, 1124678745, 1095185847, 1066588319, 1038853279, 1011949301, 985846337, 960515652, 935929751, 912062324, 888888180, 866383197, 844524266, 823289242, 802656897, 782606878, 763119661, 744176512, 725759453, 707851223, 690435245, 673495594, 657016968, 640984657, 625384520, 610202953, 595426870, 581043678, 567041253, 553407924, 540132446, 527203990, 514612116, 502346764, 490398230, 478757159, 467414524, 456361614, 445590021, 435091629, 424858598, 414883358, 405158592, 395677230, 386432438, 377417608, 368626350, 360052482, 351690023, 343533186, 335576366, 327814141, 320241256, 312852624, 305643315, 298608554, 291743710, 285044298, 278505965, 272124492, 265895787, 259815880, 253880919, 248087166, 242430991, 236908873, 231517391, 226253224, 221113145, 216094021, 211192807, 206406544, 201732356, 197167449, 192709104]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 276).prefactor = (975382143605399/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 276).cutoff/(generalMeanRows 276).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 276).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 276).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 276).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 276

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 276).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 276).criticalRate j.val*(generalMeanRows 276).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 276).c*(generalMeanRows 276).criticalPoint j.val)).2-
      (generalMeanRows 276).J/2-(generalMeanRows 276).error (generalMeanGrid j.val)+
      (generalMeanRows 276).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 276).c)).2-
      (generalMeanRows 276).J/2-(generalMeanRows 276).error 4 := by
  have he : (generalMeanRows 276).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 276) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 276)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0276

/-! Kernel-checked entropy margins for general spectral rectangle 277. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0277
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4814345490, 4639489839, 4472680896, 4313456535, 4161387264, 4016073385, 3877142454, 3744247008, 3617062531, 3495285613, 3378632293, 3266836567, 3159649020, 3056835598, 2958176480, 2863465051, 2772506969, 2685119302, 2601129743, 2520375883, 2442704552, 2367971202, 2296039342, 2226780016, 2160071321, 2095797962, 2033850833, 1974126638, 1916527529, 1860960780, 1807338474, 1755577219, 1705597877, 1657325318, 1610688183, 1565618669, 1522052325, 1479927863, 1439186976, 1399774175, 1361636630, 1324724027, 1288988426, 1254384135, 1220867590, 1188397236, 1156933424, 1126438312, 1096875764, 1068211267, 1040411844, 1013445976, 987283526, 961895670, 937254831, 913334616, 890109755, 867556050, 845650318, 824370341, 803694824, 783603344, 764076313, 745094935, 726641172, 708697704, 691247897, 674275773, 657765977, 641703748, 626074896, 610865771, 596063242, 581654670, 567627891, 553971193, 540673292, 527723321, 515110805, 502825647, 490858112, 479198811, 467838687, 456768998, 445981310, 435467477, 425219634, 415230184, 405491786, 395997348, 386740012, 377713148, 368910347, 360325405, 351952323, 343785294, 335818698, 328047093, 320465211, 313067946, 305850355, 298807648, 291935181, 285228453, 278683101, 272294893, 266059725, 259973617, 254032704, 248233239, 242571582, 237044203, 231647671, 226378656, 221233924, 216210332, 211304829, 206514448, 201836306, 197267602, 192805612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 277).prefactor = (2438956119614869/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 277).cutoff/(generalMeanRows 277).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 277).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 277).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 277).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 277

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 277).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 277).criticalRate j.val*(generalMeanRows 277).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 277).c*(generalMeanRows 277).criticalPoint j.val)).2-
      (generalMeanRows 277).J/2-(generalMeanRows 277).error (generalMeanGrid j.val)+
      (generalMeanRows 277).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 277).c)).2-
      (generalMeanRows 277).J/2-(generalMeanRows 277).error 4 := by
  have he : (generalMeanRows 277).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 277) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 277)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0277

/-! Kernel-checked entropy margins for general spectral rectangle 278. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0278
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4743242433, 4568708284, 4402240178, 4243374951, 4091682120, 3946761041, 3808238365, 3675765760, 3549017879, 3427690514, 3311498939, 3200176415, 3093472820, 2991153422, 2892997747, 2798798554, 2708360895, 2621501258, 2538046777, 2457834505, 2380710755, 2306530480, 2235156709, 2166460025, 2100318082, 2036615156, 1975241730, 1916094113, 1859074076, 1804088528, 1751049201, 1699872364, 1650478555, 1602792331, 1556742035, 1512259576, 1469280229, 1427742440, 1387587649, 1348760124, 1311206804, 1274877150, 1239723012, 1205698495, 1172759837, 1140865300, 1109975058, 1080051099, 1051057127, 1022958477, 995722025, 969316114, 943710475, 918876162, 894785479, 871411920, 848730113, 826715758, 805345578, 784597269, 764449453, 744881629, 725874137, 707408114, 689465459, 672028793, 655081430, 638607340, 622591124, 607017980, 591873679, 577144537, 562817392, 548879579, 535318910, 522123650, 509282501, 496784578, 484619394, 472776844, 461247186, 450021026, 439089305, 428443283, 418074526, 407974894, 398136528, 388551839, 379213499, 370114425, 361247774, 352606933, 344185506, 335977311, 327976367, 320176889, 312573279, 305160118, 297932162, 290884333, 284011714, 277309540, 270773199, 264398219, 258180266, 252115140, 246198768, 240427202, 234796612, 229303282, 223943609, 218714095, 213611346, 208632067, 203773060, 199031219, 194403528, 189887057, 185478963, 181176479, 176976919]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 278).prefactor = (488650477636371/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 278).cutoff/(generalMeanRows 278).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 278).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 278).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 278).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 278

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 278).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 278).criticalRate j.val*(generalMeanRows 278).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 278).c*(generalMeanRows 278).criticalPoint j.val)).2-
      (generalMeanRows 278).J/2-(generalMeanRows 278).error (generalMeanGrid j.val)+
      (generalMeanRows 278).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 278).c)).2-
      (generalMeanRows 278).J/2-(generalMeanRows 278).error 4 := by
  have he : (generalMeanRows 278).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 278) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 278)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0278

/-! Kernel-checked entropy margins for general spectral rectangle 279. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0279
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4802148643, 4627650987, 4461199656, 4302331450, 4150615929, 4005652554, 3867068146, 3734514596, 3607666828, 3486220948, 3369892583, 3258415376, 3151539621, 3049031022, 2950669563, 2856248481, 2765573318, 2678461064, 2594739364, 2514245791, 2436827179, 2362339007, 2290644831, 2221615760, 2155129970, 2091072260, 2029333628, 1969810893, 1912406333, 1857027351, 1803586170, 1751999539, 1702188468, 1654077977, 1607596861, 1562677472, 1519255515, 1477269857, 1436662350, 1397377660, 1359363114, 1322568552, 1286946187, 1252450478, 1219038010, 1186667375, 1155299070, 1124895392, 1095420347, 1066839557, 1039120178, 1012230822, 986141478, 960823448, 936249274, 912392682, 889228517, 866732690, 844882128, 823654717, 803029264, 782985445, 763503768, 744565529, 726152779, 708248285, 690835498, 673898520, 657422074, 641391475, 625792606, 610611886, 595836252, 581453132, 567450424, 553816476, 540540063, 527610374, 515016988, 502749859, 490799304, 479155981, 467810878, 456755299, 445980851, 435479430, 425243210, 415264631, 405536390, 396051426, 386802917, 377784264, 368989087, 360411214, 352044672, 343883681, 335922646, 328156151, 320578948, 313185958, 305972258, 298933075, 292063788, 285359915, 278817108, 272431155, 266197967, 260113577, 254174139, 248375917, 242715287, 237188729, 231792826, 226524260, 221379806, 216356334, 211450801, 206660251, 201981809, 197412683, 192950157]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 279).prefactor = (4884424368468543/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 279).cutoff/(generalMeanRows 279).c)).2 =
    (178128549058887/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 279).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 279).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 279).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 279

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 279).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 279).criticalRate j.val*(generalMeanRows 279).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 279).c*(generalMeanRows 279).criticalPoint j.val)).2-
      (generalMeanRows 279).J/2-(generalMeanRows 279).error (generalMeanGrid j.val)+
      (generalMeanRows 279).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 279).c)).2-
      (generalMeanRows 279).J/2-(generalMeanRows 279).error 4 := by
  have he : (generalMeanRows 279).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 279) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 279)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0279

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock03 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 3 i) := by
  fin_cases i
  · exact EntropyRow0210.numerical
  · exact EntropyRow0211.numerical
  · exact EntropyRow0212.numerical
  · exact EntropyRow0213.numerical
  · exact EntropyRow0214.numerical
  · exact EntropyRow0215.numerical
  · exact EntropyRow0216.numerical
  · exact EntropyRow0217.numerical
  · exact EntropyRow0218.numerical
  · exact EntropyRow0219.numerical
  · exact EntropyRow0220.numerical
  · exact EntropyRow0221.numerical
  · exact EntropyRow0222.numerical
  · exact EntropyRow0223.numerical
  · exact EntropyRow0224.numerical
  · exact EntropyRow0225.numerical
  · exact EntropyRow0226.numerical
  · exact EntropyRow0227.numerical
  · exact EntropyRow0228.numerical
  · exact EntropyRow0229.numerical
  · exact EntropyRow0230.numerical
  · exact EntropyRow0231.numerical
  · exact EntropyRow0232.numerical
  · exact EntropyRow0233.numerical
  · exact EntropyRow0234.numerical
  · exact EntropyRow0235.numerical
  · exact EntropyRow0236.numerical
  · exact EntropyRow0237.numerical
  · exact EntropyRow0238.numerical
  · exact EntropyRow0239.numerical
  · exact EntropyRow0240.numerical
  · exact EntropyRow0241.numerical
  · exact EntropyRow0242.numerical
  · exact EntropyRow0243.numerical
  · exact EntropyRow0244.numerical
  · exact EntropyRow0245.numerical
  · exact EntropyRow0246.numerical
  · exact EntropyRow0247.numerical
  · exact EntropyRow0248.numerical
  · exact EntropyRow0249.numerical
  · exact EntropyRow0250.numerical
  · exact EntropyRow0251.numerical
  · exact EntropyRow0252.numerical
  · exact EntropyRow0253.numerical
  · exact EntropyRow0254.numerical
  · exact EntropyRow0255.numerical
  · exact EntropyRow0256.numerical
  · exact EntropyRow0257.numerical
  · exact EntropyRow0258.numerical
  · exact EntropyRow0259.numerical
  · exact EntropyRow0260.numerical
  · exact EntropyRow0261.numerical
  · exact EntropyRow0262.numerical
  · exact EntropyRow0263.numerical
  · exact EntropyRow0264.numerical
  · exact EntropyRow0265.numerical
  · exact EntropyRow0266.numerical
  · exact EntropyRow0267.numerical
  · exact EntropyRow0268.numerical
  · exact EntropyRow0269.numerical
  · exact EntropyRow0270.numerical
  · exact EntropyRow0271.numerical
  · exact EntropyRow0272.numerical
  · exact EntropyRow0273.numerical
  · exact EntropyRow0274.numerical
  · exact EntropyRow0275.numerical
  · exact EntropyRow0276.numerical
  · exact EntropyRow0277.numerical
  · exact EntropyRow0278.numerical
  · exact EntropyRow0279.numerical
end SingularValueBounds.KL.Certificates
