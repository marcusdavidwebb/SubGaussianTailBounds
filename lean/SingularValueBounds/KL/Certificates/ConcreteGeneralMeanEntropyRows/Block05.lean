import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 350. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0350
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4807644923, 4633077062, 4466534594, 4307557160, 4155716888, 4010615564, 3871882107, 3739170302, 3612156780, 3490539182, 3374034514, 3262377655, 3155320007, 3052628259, 2954083276, 2859479073, 2768621883, 2681329304, 2597429512, 2516760547, 2439169644, 2364512629, 2292653354, 2223463176, 2156820481, 2092610234, 2030723570, 1971057413, 1913514116, 1858001136, 1804430723, 1752719637, 1702788879, 1654563445, 1607972091, 1562947120, 1519424176, 1477342055, 1436642529, 1397270180, 1359172242, 1322298459, 1286600943, 1252034050, 1218554256, 1186120045, 1154691803, 1124231717, 1094703680, 1066073202, 1038307329, 1011374559, 985244774, 959889166, 935280169, 911391404, 888197610, 865674599, 843799194, 822549187, 801903286, 781841076, 762342971, 743390182, 724964671, 707049122, 689626905, 672682042, 656199180, 640163562, 624560998, 609377838, 594600952, 580217704, 566215931, 552583919, 539310389, 526384470, 513795691, 501533956, 489589529, 477953024, 466615382, 455567866, 444802040, 434309760, 424083163, 414114653, 404396890, 394922783, 385685477, 376678344, 367894974, 359329167, 350974926, 342826445, 334878107, 327124472, 319560272, 312180407, 304979935, 297954067, 291098162, 284407723, 277878389, 271505930, 265286245, 259215357, 253289404, 247504640, 241857431, 236344247, 230961662, 225706348, 220575074, 215564700, 210672179, 205894545, 201228920, 196672505, 192222579]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 350).prefactor = (2430848165329479/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 350).cutoff/(generalMeanRows 350).c)).2 =
    (43973685107257/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 350).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 350).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 350).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 350

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 350).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 350).criticalRate j.val*(generalMeanRows 350).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 350).c*(generalMeanRows 350).criticalPoint j.val)).2-
      (generalMeanRows 350).J/2-(generalMeanRows 350).error (generalMeanGrid j.val)+
      (generalMeanRows 350).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 350).c)).2-
      (generalMeanRows 350).J/2-(generalMeanRows 350).error 4 := by
  have he : (generalMeanRows 350).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 350) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 350)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0350

/-! Kernel-checked entropy margins for general spectral rectangle 351. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0351
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4817883009, 4642989171, 4476127612, 4316838118, 4164692933, 4019293925, 3880270069, 3747275184, 3619985906, 3498099867, 3381334045, 3269423271, 3162118886, 3059187509, 2960409917, 2865580032, 2774503982, 2686999254, 2602893907, 2522025856, 2444242209, 2369398660, 2297358924, 2227994223, 2161182800, 2096809483, 2034765263, 1974946922, 1917256673, 1861601829, 1807894502, 1756051311, 1705993120, 1657644787, 1610934935, 1565795732, 1522162693, 1479974485, 1439172755, 1399701960, 1361509215, 1324544142, 1288758741, 1254107252, 1220546042, 1188033488, 1156529870, 1125997274, 1096399492, 1067701940, 1039871566, 1012876782, 986687377, 961274459, 936610379, 912668675, 889424012, 866852121, 844929755, 823634633, 802945396, 782841561, 763303479, 744312297, 725849919, 707898970, 690442763, 673465268, 656951079, 640885389, 625253957, 610043089, 595239610, 580830839, 566804571, 553149052, 539852964, 526905400, 514295851, 502014186, 490050638, 478395786, 467040543, 455976140, 445194112, 434686289, 424444781, 414461966, 404730480, 395243209, 385993274, 376974026, 368179035, 359602080, 351237144, 343078404, 335120224, 327357147, 319783890, 312395336, 305186528, 298152663, 291289087, 284591287, 278054891, 271675656, 265449471, 259372345, 253440406, 247649899, 241997179, 236478706, 231091045, 225830860, 220694910, 215680050, 210783220, 206001452, 201331858, 196771633, 192318048]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 351).prefactor = (4862615398537063/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 351).cutoff/(generalMeanRows 351).c)).2 =
    (175152349795239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 351).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 351).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 351).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 351

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 351).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 351).criticalRate j.val*(generalMeanRows 351).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 351).c*(generalMeanRows 351).criticalPoint j.val)).2-
      (generalMeanRows 351).J/2-(generalMeanRows 351).error (generalMeanGrid j.val)+
      (generalMeanRows 351).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 351).c)).2-
      (generalMeanRows 351).J/2-(generalMeanRows 351).error 4 := by
  have he : (generalMeanRows 351).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 351) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 351)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0351

/-! Kernel-checked entropy margins for general spectral rectangle 352. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0352
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4826439320, 4651234879, 4484076983, 4324504600, 4172089212, 4026431983, 3887161228, 3753930150, 3626414814, 3504312312, 3387339119, 3275229598, 3167734646, 3064620467, 2965667452, 2870669153, 2779431357, 2691771226, 2607516512, 2526504843, 2448583057, 2373606589, 2301438915, 2231951025, 2165020949, 2100533308, 2038378901, 1978454326, 1920661622, 1864907938, 1811105229, 1759169967, 1709022875, 1660588678, 1613795872, 1568576505, 1524865975, 1482602843, 1441728651, 1402187759, 1363927185, 1326896464, 1291047510, 1256334481, 1222713669, 1190143374, 1158583808, 1127996987, 1098346641, 1069598123, 1041718325, 1014675598, 988439683, 962981633, 938273751, 914289528, 891003583, 868391605, 846430307, 825097366, 804371386, 784231847, 764659066, 745634157, 727138991, 709156162, 691668954, 674661308, 658117791, 642023568, 626364376, 611126494, 596296724, 581862364, 567811186, 554131416, 540811715, 527841157, 515209214, 502905737, 490920943, 479245393, 467869983, 456785930, 445984754, 435458270, 425198573, 415198029, 405449261, 395945140, 386678778, 377643512, 368832901, 360240714, 351860923, 343687693, 335715380, 327938516, 320351810, 312950134, 305728524, 298682167, 291806401, 285096707, 278548702, 272158138, 265920896, 259832976, 253890503, 248089713, 242426953, 236898680, 231501451, 226231924, 221086853, 216063086, 211157561, 206367300, 201689413, 197121089, 192659595]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 352).prefactor = (4871251151885627/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 352).cutoff/(generalMeanRows 352).c)).2 =
    (175152349795239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 352).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 352).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 352).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 352

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 352).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 352).criticalRate j.val*(generalMeanRows 352).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 352).c*(generalMeanRows 352).criticalPoint j.val)).2-
      (generalMeanRows 352).J/2-(generalMeanRows 352).error (generalMeanGrid j.val)+
      (generalMeanRows 352).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 352).c)).2-
      (generalMeanRows 352).J/2-(generalMeanRows 352).error 4 := by
  have he : (generalMeanRows 352).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 352) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 352)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0352

/-! Kernel-checked entropy margins for general spectral rectangle 353. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0353
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5304869243, 5138548384, 4979634677, 4827696192, 4682331937, 4543169156, 4409860918, 4282083953, 4159536711, 4041937617, 3929023494, 3820548129, 3716280986, 3616006023, 3519520625, 3426634620, 3337169394, 3250957062, 3167839727, 3087668785, 3010304294, 2935614390, 2863474746, 2793768079, 2726383688, 2661217030, 2598169326, 2537147197, 2478062325, 2420831134, 2365374506, 2311617500, 2259489105, 2208922001, 2159852337, 2112219529, 2065966066, 2021037332, 1977381436, 1934949057, 1893693297, 1853569542, 1814535336, 1776550256, 1739575805, 1703575298, 1668513768, 1634357871, 1601075796, 1568637183, 1537013049, 1506175707, 1476098706, 1446756760, 1418125687, 1390182356, 1362904629, 1336271311, 1310262103, 1284857552, 1260039016, 1235788617, 1212089204, 1188924318, 1166278161, 1144135556, 1122481925, 1101303254, 1080586069, 1060317410, 1040484807, 1021076253, 1002080190, 983485479, 965281390, 947457574, 930004054, 912911202, 896169727, 879770660, 863705335, 847965383, 832542713, 817429504, 802618190, 788101452, 773872207, 759923597, 746248979, 732841919, 719696181, 706805721, 694164677, 681767362, 669608260, 657682015, 645983429, 634507452, 623249179, 612203844, 601366814, 590733586, 580299779, 570061131, 560013497, 550152841, 540475235, 530976854, 521653972, 512502960, 503520281, 494702488, 486046220, 477548202, 469205237, 461014208, 452972075, 445075869, 437322694, 429709722, 422234191]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 353).prefactor = (1151730536542697/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 353).cutoff/(generalMeanRows 353).c)).2 =
    (440792956175007/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 353).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 353).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 353).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 353

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 353).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 353).criticalRate j.val*(generalMeanRows 353).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 353).c*(generalMeanRows 353).criticalPoint j.val)).2-
      (generalMeanRows 353).J/2-(generalMeanRows 353).error (generalMeanGrid j.val)+
      (generalMeanRows 353).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 353).c)).2-
      (generalMeanRows 353).J/2-(generalMeanRows 353).error 4 := by
  have he : (generalMeanRows 353).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 353) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 353)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0353

/-! Kernel-checked entropy margins for general spectral rectangle 354. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0354
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5322669148, 5155790218, 4996343293, 4843894995, 4698042986, 4558413260, 4424657721, 4296452014, 4173493579, 4055499894, 3942206900, 3833367558, 3728750558, 3628139134, 3531329989, 3438132316, 3348366898, 3261865291, 3178469064, 3098029118, 3020405039, 2945464521, 2873082820, 2803142260, 2735531768, 2670146450, 2606887197, 2545660316, 2486377190, 2428953967, 2373311260, 2319373878, 2267070572, 2216333795, 2167099484, 2119306849, 2072898188, 2027818701, 1984016322, 1941441566, 1900047376, 1859788991, 1820623809, 1782511275, 1745412760, 1709291458, 1674112283, 1639841779, 1606448029, 1573900573, 1542170327, 1511229514, 1481051593, 1451611193, 1422884051, 1394846960, 1367477705, 1340755023, 1314658543, 1289168751, 1264266939, 1239935170, 1216156236, 1192913623, 1170191479, 1147974577, 1126248289, 1104998556, 1084211857, 1063875189, 1043976039, 1024502362, 1005442560, 986785457, 968520285, 950636664, 933124580, 915974375, 899176726, 882722633, 866603403, 850810637, 835336218, 820172298, 805311287, 790745840, 776468850, 762473437, 748752935, 735300889, 722111043, 709177330, 696493870, 684054958, 671855057, 659888795, 648150955, 636636471, 625340423, 614258027, 603384635, 592715728, 582246911, 571973908, 561892560, 551998818, 542288740, 532758488, 523404325, 514222607, 505209788, 496362407, 487677095, 479150562, 470779603, 462561091, 454491973, 446569272, 438790082, 431151565, 423650951]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 354).prefactor = (577797520812859/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 354).cutoff/(generalMeanRows 354).c)).2 =
    (440792956175007/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 354).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 354).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 354).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 354

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 354).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 354).criticalRate j.val*(generalMeanRows 354).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 354).c*(generalMeanRows 354).criticalPoint j.val)).2-
      (generalMeanRows 354).J/2-(generalMeanRows 354).error (generalMeanGrid j.val)+
      (generalMeanRows 354).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 354).c)).2-
      (generalMeanRows 354).J/2-(generalMeanRows 354).error 4 := by
  have he : (generalMeanRows 354).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 354) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 354)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0354

/-! Kernel-checked entropy margins for general spectral rectangle 355. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0355
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5267451566, 5099616211, 4939248970, 4785917092, 4639218698, 4498780093, 4364253356, 4235314181, 4111659948, 3993007979, 3879093961, 3769670530, 3664505974, 3563383063, 3466097983, 3372459357, 3282287360, 3195412899, 3111676867, 3030929456, 2953029528, 2877844030, 2805247457, 2735121362, 2667353891, 2601839368, 2538477892, 2477174982, 2417841235, 2360392012, 2304747148, 2250830679, 2198570587, 2147898570, 2098749815, 2051062798, 2004779089, 1959843174, 1916202288, 1873806256, 1832607348, 1792560140, 1753621387, 1715749899, 1678906430, 1643053572, 1608155651, 1574178636, 1541090053, 1508858896, 1477455552, 1446851729, 1417020386, 1387935663, 1359572827, 1331908210, 1304919154, 1278583961, 1252881845, 1227792885, 1203297979, 1179378811, 1156017805, 1133198090, 1110903468, 1089118382, 1067827880, 1047017592, 1026673698, 1006782905, 987332419, 968309926, 949703567, 931501916, 913693963, 896269094, 879217072, 862528023, 846192416, 830201051, 814545043, 799215809, 784205053, 769504758, 755107169, 741004785, 727190349, 713656835, 700397440, 687405577, 674674860, 662199105, 649972312, 637988666, 626242526, 614728417, 603441026, 592375195, 581525915, 570888319, 560457681, 550229404, 540199024, 530362195, 520714694, 511252410, 501971344, 492867604, 483937399, 475177039, 466582931, 458151572, 449879551, 441763541, 433800303, 425986675, 418319576, 410795999, 403413011, 396167752, 389057428]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 355).prefactor = (2312424337449059/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 355).cutoff/(generalMeanRows 355).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 355).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 355).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 355).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 355

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 355).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 355).criticalRate j.val*(generalMeanRows 355).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 355).c*(generalMeanRows 355).criticalPoint j.val)).2-
      (generalMeanRows 355).J/2-(generalMeanRows 355).error (generalMeanGrid j.val)+
      (generalMeanRows 355).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 355).c)).2-
      (generalMeanRows 355).J/2-(generalMeanRows 355).error 4 := by
  have he : (generalMeanRows 355).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 355) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 355)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0355

/-! Kernel-checked entropy margins for general spectral rectangle 356. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0356
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5341388516, 5173901739, 5013860061, 4860830406, 4714410668, 4574227012, 4439931456, 4311199708, 4187729227, 4069237469, 3955460312, 3846150625, 3741076976, 3640022451, 3542783582, 3449169371, 3359000393, 3272107981, 3188333470, 3107527511, 3029549439, 2954266683, 2881554231, 2811294135, 2743375046, 2677691792, 2614144985, 2552640653, 2493089902, 2435408601, 2379517089, 2325339903, 2272805523, 2221846138, 2172397421, 2124398327, 2077790899, 2032520089, 1988533588, 1945781672, 1904217052, 1863794737, 1824471906, 1786207786, 1748963536, 1712702145, 1677388327, 1642988433, 1609470356, 1576803451, 1544958459, 1513907428, 1483623651, 1454081594, 1425256838, 1397126023, 1369666788, 1342857726, 1316678330, 1291108953, 1266130759, 1241725686, 1217876408, 1194566294, 1171779381, 1149500335, 1127714425, 1106407489, 1085565914, 1065176603, 1045226953, 1025704834, 1006598563, 987896888, 969588963, 951664332, 934112914, 916924981, 900091144, 883602341, 867449818, 851625118, 836120068, 820926766, 806037571, 791445089, 777142165, 763121873, 749377505, 735902561, 722690747, 709735957, 697032273, 684573954, 672355431, 660371298, 648616306, 637085361, 625773511, 614675946, 603787992, 593105105, 582622864, 572336971, 562243243, 552337611, 542616112, 533074888, 523710184, 514518338, 505495785, 496639050, 487944745, 479409568, 471030298, 462803793, 454726989, 446796895, 439010592, 431365232, 423858032]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 356).prefactor = (462362690426743/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 356).cutoff/(generalMeanRows 356).c)).2 =
    (17513549771103/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 356).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 356).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 356).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 356

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 356).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 356).criticalRate j.val*(generalMeanRows 356).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 356).c*(generalMeanRows 356).criticalPoint j.val)).2-
      (generalMeanRows 356).J/2-(generalMeanRows 356).error (generalMeanGrid j.val)+
      (generalMeanRows 356).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 356).c)).2-
      (generalMeanRows 356).J/2-(generalMeanRows 356).error 4 := by
  have he : (generalMeanRows 356).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 356) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 356)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0356

/-! Kernel-checked entropy margins for general spectral rectangle 357. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0357
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5266516154, 5098718162, 4938400717, 4785129287, 4638500395, 4498138899, 4363695575, 4234844947, 4111283343, 3992727140, 3878911183, 3769587352, 3664523264, 3563501094, 3466316498, 3372777635, 3282704270, 3195926952, 3112286264, 3031632130, 2953823181, 2878726169, 2806215428, 2736172374, 2668485047, 2603047681, 2539760314, 2478528417, 2419262559, 2361878086, 2306294833, 2252436847, 2200232132, 2149612416, 2100512926, 2052872183, 2006631811, 1961736354, 1918133107, 1875771963, 1834605260, 1794587647, 1755675953, 1717829062, 1681007807, 1645174855, 1610294611, 1576333124, 1543257994, 1511038294, 1479644490, 1449048365, 1419222951, 1390142465, 1361782246, 1334118696, 1307129229, 1280792214, 1255086933, 1229993529, 1205492966, 1181566987, 1158198077, 1135369425, 1113064889, 1091268965, 1069966756, 1049143943, 1028786755, 1008881947, 989416772, 970378961, 951756695, 933538592, 915713681, 898271385, 881201506, 864494202, 848139978, 832129665, 816454408, 801105655, 786075139, 771354867, 756937112, 742814397, 728979488, 715425382, 702145296, 689132663, 676381118, 663884493, 651636807, 639632260, 627865226, 616330246, 605022020, 593935403, 583065398, 572407151, 561955945, 551707195, 541656444, 531799358, 522131719, 512649427, 503348490, 494225020, 485275235, 476495450, 467882077, 459431619, 451140668, 443005903, 435024087, 427192063, 419506752, 411965150, 404564328, 397301426, 390173653]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 357).prefactor = (2319632712579889/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 357).cutoff/(generalMeanRows 357).c)).2 =
    (214919350805249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 357).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 357).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 357).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 357

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 357).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 357).criticalRate j.val*(generalMeanRows 357).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 357).c*(generalMeanRows 357).criticalPoint j.val)).2-
      (generalMeanRows 357).J/2-(generalMeanRows 357).error (generalMeanGrid j.val)+
      (generalMeanRows 357).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 357).c)).2-
      (generalMeanRows 357).J/2-(generalMeanRows 357).error 4 := by
  have he : (generalMeanRows 357).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 357) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 357)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0357

/-! Kernel-checked entropy margins for general spectral rectangle 358. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0358
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5285411381, 5117003777, 4956089751, 4802235075, 4655036501, 4514119059, 4379133641, 4249754837, 4125678995, 4006622472, 3892320056, 3782523536, 3677000412, 3575532715, 3477915933, 3383958039, 3293478593, 3206307926, 3122286388, 3041263663, 2963098129, 2887656279, 2814812182, 2744446986, 2676448457, 2610710556, 2547133044, 2485621117, 2426085066, 2368439966, 2312605376, 2258505074, 2206066797, 2155222009, 2105905678, 2058056068, 2011614550, 1966525423, 1922735739, 1880195154, 1838855775, 1798672023, 1759600505, 1721599891, 1684630802, 1648655700, 1613638791, 1579545930, 1546344528, 1514003476, 1482493060, 1451784891, 1421851835, 1392667945, 1364208404, 1336449462, 1309368385, 1282943400, 1257153650, 1231979147, 1207400724, 1183400002, 1159959344, 1137061823, 1114691186, 1092831822, 1071468728, 1050587486, 1030174228, 1010215615, 990698811, 971611459, 952941660, 934677949, 916809278, 899324998, 882214836, 865468884, 849077580, 833031691, 817322303, 801940802, 786878866, 772128448, 757681769, 743531303, 729669765, 716090107, 702785504, 689749343, 676975220, 664456928, 652188447, 640163942, 628377752, 616824385, 605498509, 594394948, 583508676, 572834810, 562368608, 552105458, 542040877, 532170509, 522490114, 512995568, 503682857, 494548077, 485587424, 476797195, 468173784, 459713678, 451413452, 443269771, 435279381, 427439112, 419745871, 412196642, 404788481, 397518519, 390383952]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 358).prefactor = (2320308740967619/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 358).cutoff/(generalMeanRows 358).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 358).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 358).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 358).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 358

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 358).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 358).criticalRate j.val*(generalMeanRows 358).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 358).c*(generalMeanRows 358).criticalPoint j.val)).2-
      (generalMeanRows 358).J/2-(generalMeanRows 358).error (generalMeanGrid j.val)+
      (generalMeanRows 358).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 358).c)).2-
      (generalMeanRows 358).J/2-(generalMeanRows 358).error 4 := by
  have he : (generalMeanRows 358).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 358) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 358)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0358

/-! Kernel-checked entropy margins for general spectral rectangle 359. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0359
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5303432432, 5134450628, 4972987953, 4818608696, 4670908236, 4529510324, 4394064662, 4264244731, 4139745842, 4020283386, 3905591245, 3795420365, 3689537452, 3587723791, 3489774177, 3395495926, 3304707983, 3217240100, 3132932084, 3051633105, 2973201059, 2897501983, 2824409519, 2753804407, 2685574031, 2619611991, 2555817706, 2494096049, 2434357005, 2376515359, 2320490397, 2266205635, 2213588566, 2162570418, 2113085938, 2065073181, 2018473318, 1973230455, 1929291467, 1886605837, 1845125507, 1804804745, 1765600009, 1727469829, 1690374691, 1654276929, 1619140627, 1584931523, 1551616919, 1519165597, 1487547743, 1456734873, 1426699757, 1397416363, 1368859786, 1341006198, 1313832785, 1287317702, 1261440021, 1236179682, 1211517458, 1187434903, 1163914322, 1140938730, 1118491819, 1096557923, 1075121990, 1054169551, 1033686693, 1013660029, 994076681, 974924250, 956190794, 937864811, 919935216, 902391321, 885222821, 868419773, 851972581, 835871982, 820109031, 804675086, 789561795, 774761085, 760265149, 746066435, 732157635, 718531676, 705181710, 692101101, 679283424, 666722449, 654412138, 642346634, 630520259, 618927499, 607563006, 596421587, 585498197, 574787938, 564286050, 553987907, 543889011, 533984989, 524271588, 514744669, 505400206, 496234280, 487243075, 478422875, 469770062, 461281110, 452952584, 444781136, 436763503, 428896502, 421177030, 413602061, 406168641, 398873891, 391714998]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 359).prefactor = (186257602161371/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 359).cutoff/(generalMeanRows 359).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 359).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 359).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 359).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 359

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 359).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 359).criticalRate j.val*(generalMeanRows 359).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 359).c*(generalMeanRows 359).criticalPoint j.val)).2-
      (generalMeanRows 359).J/2-(generalMeanRows 359).error (generalMeanGrid j.val)+
      (generalMeanRows 359).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 359).c)).2-
      (generalMeanRows 359).J/2-(generalMeanRows 359).error 4 := by
  have he : (generalMeanRows 359).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 359) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 359)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0359

/-! Kernel-checked entropy margins for general spectral rectangle 360. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0360
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5360749381, 5192622056, 5031925774, 4878231419, 4731140432, 4590282140, 4455311381, 4325906363, 4201766760, 4082611978, 3968179608, 3858224018, 3752515072, 3650836976, 3552987219, 3458775611, 3368023406, 3280562487, 3196234638, 3114890857, 3036390736, 2960601882, 2887399394, 2816665363, 2748288428, 2682163354, 2618190641, 2556276168, 2496330856, 2438270361, 2382014779, 2327488383, 2274619369, 2223339624, 2173584506, 2125292644, 2078405746, 2032868419, 1988628008, 1945634437, 1903840061, 1863199536, 1823669684, 1785209380, 1747779430, 1711342477, 1675862890, 1641306678, 1607641401, 1574836085, 1542861147, 1511688318, 1481290580, 1451642096, 1422718151, 1394495094, 1366950284, 1340062038, 1313809583, 1288173011, 1263133235, 1238671949, 1214771587, 1191415292, 1168586877, 1146270793, 1124452099, 1103116436, 1082249994, 1061839489, 1041872138, 1022335637, 1003218135, 984508217, 966194883, 948267528, 930715926, 913530210, 896700860, 880218685, 864074809, 848260659, 832767947, 817588666, 802715069, 788139665, 773855203, 759854666, 746131260, 732678404, 719489721, 706559033, 693880348, 681447857, 669255924, 657299081, 645572021, 634069591, 622786786, 611718745, 600860745, 590208193, 579756627, 569501706, 559439208, 549565025, 539875158, 530365718, 521032913, 511873056, 502882550, 494057895, 485395676, 476892568, 468545326, 460350789, 452305870, 444407562, 436652927, 429039100, 421563284]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 360).prefactor = (919063031589207/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 360).cutoff/(generalMeanRows 360).c)).2 =
    (21451405729771/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 360).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 360).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 360).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 360

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 360).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 360).criticalRate j.val*(generalMeanRows 360).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 360).c*(generalMeanRows 360).criticalPoint j.val)).2-
      (generalMeanRows 360).J/2-(generalMeanRows 360).error (generalMeanGrid j.val)+
      (generalMeanRows 360).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 360).c)).2-
      (generalMeanRows 360).J/2-(generalMeanRows 360).error 4 := by
  have he : (generalMeanRows 360).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 360) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 360)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0360

/-! Kernel-checked entropy margins for general spectral rectangle 361. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0361
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5305037338, 5136003924, 4974463327, 4819983454, 4672162953, 4530628529, 4395032547, 4265050891, 4140381033, 4020740306, 3905864335, 3795505622, 3689432267, 3587426798, 3489285108, 3394815491, 3303837752, 3216182400, 3131689900, 3050209997, 2971601082, 2895729617, 2822469599, 2751702071, 2683314665, 2617201178, 2553261186, 2491399678, 2431526722, 2373557154, 2317410282, 2263009621, 2210282640, 2159160522, 2109577954, 2061472913, 2014786480, 1969462663, 1925448223, 1882692523, 1841147382, 1800766932, 1761507494, 1723327457, 1686187162, 1650048798, 1614876300, 1580635258, 1547292823, 1514817630, 1483179717, 1452350451, 1422302460, 1393009565, 1364446723, 1336589964, 1309416340, 1282903870, 1257031495, 1231779030, 1207127120, 1183057199, 1159551453, 1136592783, 1114164768, 1092251634, 1070838225, 1049909968, 1029452853, 1009453399, 989898635, 970776073, 952073688, 933779893, 915883525, 898373821, 881240401, 864473253, 848062714, 831999456, 816274471, 800879059, 785804811, 771043601, 756587568, 742429112, 728560879, 714975749, 701666831, 688627450, 675851141, 663331639, 651062868, 639038942, 627254147, 615702943, 604379952, 593279954, 582397881, 571728810, 561267958, 551010679, 540952455, 531088895, 521415728, 511928800, 502624069, 493497601, 484545569, 475764243, 467149995, 458699287, 450408676, 442274805, 434294401, 426464276, 418781319, 411242498, 403844856, 396585505, 389461630]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 361).prefactor = (4627218232346357/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 361).cutoff/(generalMeanRows 361).c)).2 =
    (52628508991043/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 361).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 361).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 361).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 361

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 361).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 361).criticalRate j.val*(generalMeanRows 361).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 361).c*(generalMeanRows 361).criticalPoint j.val)).2-
      (generalMeanRows 361).J/2-(generalMeanRows 361).error (generalMeanGrid j.val)+
      (generalMeanRows 361).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 361).c)).2-
      (generalMeanRows 361).J/2-(generalMeanRows 361).error 4 := by
  have he : (generalMeanRows 361).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 361) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 361)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0361

/-! Kernel-checked entropy margins for general spectral rectangle 362. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0362
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5251842974, 5081928969, 4919541138, 4764248060, 4615648895, 4473370712, 4337066109, 4206411081, 4081103105, 3960859416, 3845415454, 3734523460, 3627951197, 3525480795, 3426907693, 3332039681, 3240696017, 3152706623, 3067911349, 2986159293, 2907308176, 2831223770, 2757779369, 2686855296, 2618338455, 2552121908, 2488104490, 2426190450, 2366289113, 2308314573, 2252185400, 2197824376, 2145158242, 2094117463, 2044636012, 1996651164, 1950103308, 1904935768, 1861094635, 1818528615, 1777188877, 1737028922, 1698004449, 1660073240, 1623195041, 1587331460, 1552445867, 1518503298, 1485470365, 1453315178, 1422007263, 1391517490, 1361818001, 1332882150, 1304684432, 1277200437, 1250406783, 1224281072, 1198801841, 1173948509, 1149701341, 1126041405, 1102950527, 1080411264, 1058406860, 1036921220, 1015938874, 995444949, 975425142, 955865693, 936753359, 918075391, 899819510, 881973890, 864527131, 847468245, 830786637, 814472084, 798514723, 782905034, 767633823, 752692213, 738071622, 723763761, 709760614, 696054427, 682637702, 669503181, 656643842, 644052882, 631723715, 619649959, 607825431, 596244135, 584900259, 573788167, 562902390, 552237620, 541788707, 531550649, 521518591, 511687813, 502053732, 492611893, 483357967, 474287741, 465397121, 456682125, 448138875, 439763601, 431552630, 423502390, 415609398, 407870265, 400281687, 392840448, 385543411, 378387519, 371369792, 364487324, 357737282]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 362).prefactor = (2314745428412053/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 362).cutoff/(generalMeanRows 362).c)).2 =
    (81452120404363/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 362).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 362).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 362).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 362

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 362).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 362).criticalRate j.val*(generalMeanRows 362).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 362).c*(generalMeanRows 362).criticalPoint j.val)).2-
      (generalMeanRows 362).J/2-(generalMeanRows 362).error (generalMeanGrid j.val)+
      (generalMeanRows 362).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 362).c)).2-
      (generalMeanRows 362).J/2-(generalMeanRows 362).error 4 := by
  have he : (generalMeanRows 362).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 362) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 362)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0362

/-! Kernel-checked entropy margins for general spectral rectangle 363. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0363
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5111576141, 4941197001, 4778415681, 4622797547, 4473938716, 4331463375, 4195021384, 4064286133, 3938952617, 3818735708, 3703368589, 3592601341, 3486199663, 3383943708, 3285627021, 3191055573, 3100046876, 3012429178, 2928040717, 2846729038, 2768350372, 2692769056, 2619856997, 2549493186, 2481563239, 2415958981, 2352578048, 2291323535, 2232103651, 2174831415, 2119424357, 2065804256, 2013896881, 1963631761, 1914941963, 1867763888, 1822037077, 1777704039, 1734710073, 1693003122, 1652533617, 1613254344, 1575120314, 1538088641, 1502118428, 1467170661, 1433208107, 1400195219, 1368098051, 1336884169, 1306522575, 1276983632, 1248238996, 1220261545, 1193025323, 1166505477, 1140678203, 1115520695, 1091011092, 1067128435, 1043852623, 1021164368, 999045159, 977477221, 956443486, 935927553, 915913660, 896386654, 877331960, 858735559, 840583957, 822864167, 805563680, 788670448, 772172860, 756059725, 740320253, 724944037, 709921035, 695241556, 680896246, 666876069, 653172300, 639776505, 626680534, 613876508, 601356806, 589114056, 577141124, 565431106, 553977317, 542773283, 531812734, 521089591, 510597967, 500332151, 490286608, 480455967, 470835017, 461418705, 452202121, 443180502, 434349221, 425703785, 417239827, 408953104, 400839493, 392894985, 385115682, 377497792, 370037629, 362731604, 355576226, 348568095, 341703904, 334980431, 328394539, 321943173, 315623356, 309432187, 303366841]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 363).prefactor = (1165540724440251/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 363).cutoff/(generalMeanRows 363).c)).2 =
    (195787002927057/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 363).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 363).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 363).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 363

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 363).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 363).criticalRate j.val*(generalMeanRows 363).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 363).c*(generalMeanRows 363).criticalPoint j.val)).2-
      (generalMeanRows 363).J/2-(generalMeanRows 363).error (generalMeanGrid j.val)+
      (generalMeanRows 363).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 363).c)).2-
      (generalMeanRows 363).J/2-(generalMeanRows 363).error 4 := by
  have he : (generalMeanRows 363).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 363) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 363)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0363

/-! Kernel-checked entropy margins for general spectral rectangle 364. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0364
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5160930418, 4991371590, 4829376997, 4674511455, 4526370685, 4384578613, 4248784964, 4118663109, 3993908127, 3874235063, 3759377359, 3649085429, 3543125371, 3441277794, 3343336752, 3249108771, 3158411958, 3071075186, 2986937351, 2905846681, 2827660110, 2752242691, 2679467066, 2609212967, 2541366763, 2475821030, 2412474165, 2351230016, 2291997551, 2234690540, 2179227261, 2125530232, 2073525959, 2023144692, 1974320216, 1926989633, 1881093182, 1836574048, 1793378204, 1751454245, 1710753246, 1671228623, 1632836001, 1595533095, 1559279594, 1524037057, 1489768808, 1456439845, 1424016749, 1392467602, 1361761905, 1331870508, 1302765537, 1274420331, 1246809375, 1219908249, 1193693566, 1168142922, 1143234849, 1118948766, 1095264938, 1072164430, 1049629073, 1027641422, 1006184728, 985242895, 964800460, 944842553, 925354876, 906323674, 887735709, 869578238, 851838988, 834506138, 817568295, 801014477, 784834095, 769016934, 753553136, 738433189, 723647907, 709188417, 695046148, 681212816, 667680411, 654441191, 641487662, 628812577, 616408919, 604269895, 592388928, 580759643, 569375867, 558231612, 547321077, 536638634, 526178824, 515936349, 505906068, 496082992, 486462273, 477039205, 467809214, 458767858, 449910818, 441233894, 432733004, 424404177, 416243550, 408247365, 400411962, 392733781, 385209355, 377835308, 370608352, 363525282, 356582979, 349778399, 343108579, 336570628, 330161727]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 364).prefactor = (582417849315929/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 364).cutoff/(generalMeanRows 364).c)).2 =
    (405217465901701/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 364).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 364).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 364).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 364

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 364).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 364).criticalRate j.val*(generalMeanRows 364).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 364).c*(generalMeanRows 364).criticalPoint j.val)).2-
      (generalMeanRows 364).J/2-(generalMeanRows 364).error (generalMeanGrid j.val)+
      (generalMeanRows 364).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 364).c)).2-
      (generalMeanRows 364).J/2-(generalMeanRows 364).error 4 := by
  have he : (generalMeanRows 364).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 364) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 364)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0364

/-! Kernel-checked entropy margins for general spectral rectangle 365. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0365
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5022571339, 4852639222, 4690341671, 4535240270, 4386927678, 4245024920, 4109178968, 3979060572, 3854362315, 3734796865, 3620095392, 3510006141, 3404293135, 3302734996, 3205123876, 3111264474, 3020973145, 2934077083, 2850413567, 2769829270, 2692179632, 2617328270, 2545146440, 2475512543, 2408311660, 2343435130, 2280780158, 2220249440, 2161750835, 2105197040, 2050505302, 1997597141, 1946398100, 1896837502, 1848848233, 1802366532, 1757331800, 1713686417, 1671375575, 1630347118, 1590551396, 1551941122, 1514471246, 1478098829, 1442782931, 1408484501, 1375166277, 1342792690, 1311329775, 1280745086, 1251007617, 1222087727, 1193957070, 1166588529, 1139956152, 1114035093, 1088801560, 1064232757, 1040306838, 1017002859, 994300735, 972181196, 950625749, 929616641, 909136820, 889169909, 869700166, 850712460, 832192239, 814125506, 796498790, 779299126, 762514029, 746131474, 730139874, 714528060, 699285268, 684401111, 669865574, 655668989, 641802024, 628255669, 615021220, 602090269, 589454689, 577106624, 565038477, 553242900, 541712782, 530441244, 519421624, 508647471, 498112539, 487810775, 477736313, 467883468, 458246726, 448820743, 439600332, 430580461, 421756248, 413122952, 404675971, 396410835, 388323202, 380408855, 372663695, 365083737, 357665108, 350404042, 343296876, 336340047, 329530088, 322863627, 316337379, 309948150, 303692827, 297568380, 291571859, 285700388, 279951167]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 365).prefactor = (293230648885809/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 365).cutoff/(generalMeanRows 365).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 365).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 365).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 365).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 365

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 365).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 365).criticalRate j.val*(generalMeanRows 365).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 365).c*(generalMeanRows 365).criticalPoint j.val)).2-
      (generalMeanRows 365).J/2-(generalMeanRows 365).error (generalMeanGrid j.val)+
      (generalMeanRows 365).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 365).c)).2-
      (generalMeanRows 365).J/2-(generalMeanRows 365).error 4 := by
  have he : (generalMeanRows 365).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 365) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 365)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0365

/-! Kernel-checked entropy margins for general spectral rectangle 366. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0366
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4976888532, 4806190069, 4643159866, 4487359940, 4338383239, 4195850948, 4059410078, 3928731311, 3803507069, 3683449768, 3568290253, 3457776371, 3351671689, 3249754318, 3151815849, 3057660384, 2967103642, 2879972150, 2796102496, 2715340641, 2637541294, 2562567327, 2490289242, 2420584677, 2353337945, 2288439617, 2225786125, 2165279401, 2106826536, 2050339469, 1995734693, 1942932987, 1891859154, 1842441794, 1794613078, 1748308543, 1703466899, 1660029849, 1617941923, 1577150314, 1537604735, 1499257282, 1462062295, 1425976247, 1390957619, 1356966800, 1323965983, 1291919066, 1260791569, 1230550543, 1201164498, 1172603320, 1144838205, 1117841593, 1091587103, 1066049475, 1041204514, 1017029035, 993500819, 970598559, 948301819, 926590995, 905447266, 884852567, 864789545, 845241531, 826192506, 807627068, 789530408, 771888281, 754686977, 737913304, 721554558, 705598501, 690033348, 674847737, 660030718, 645571730, 631460588, 617687464, 604242872, 591117656, 578302973, 565790282, 553571329, 541638139, 529983000, 518598457, 507477297, 496612541, 485997438, 475625449, 465490247, 455585701, 445905872, 436445008, 427197531, 418158037, 409321282, 400682184, 392235810, 383977375, 375902236, 368005885, 360283944, 352732163, 345346414, 338122687, 331057082, 324145815, 317385201, 310771662, 304301717, 297971980, 291779158, 285720048, 279791530, 273990570, 268314216, 262759590, 257323894]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 366).prefactor = (4695065517457429/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 366).cutoff/(generalMeanRows 366).c)).2 =
    (188064841713321/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 366).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 366).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 366).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 366

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 366).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 366).criticalRate j.val*(generalMeanRows 366).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 366).c*(generalMeanRows 366).criticalPoint j.val)).2-
      (generalMeanRows 366).J/2-(generalMeanRows 366).error (generalMeanGrid j.val)+
      (generalMeanRows 366).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 366).c)).2-
      (generalMeanRows 366).J/2-(generalMeanRows 366).error 4 := by
  have he : (generalMeanRows 366).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 366) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 366)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0366

/-! Kernel-checked entropy margins for general spectral rectangle 367. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0367
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5128129027, 4957161054, 4793831882, 4637703506, 4488368952, 4345449575, 4208592633, 4077469132, 3951771878, 3831213735, 3715526040, 3604457182, 3497771306, 3395247138, 3296676912, 3201865399, 3110629007, 3022794972, 2938200602, 2856692592, 2778126392, 2702365622, 2629281534, 2558752518, 2490663642, 2424906224, 2361377443, 2299979970, 2240621632, 2183215095, 2127677570, 2073930543, 2021899516, 1971513777, 1922706170, 1875412896, 1829573316, 1785129770, 1742027410, 1700214041, 1659639972, 1620257878, 1582022670, 1544891370, 1508823002, 1473778477, 1439720497, 1406613457, 1374423356, 1343117716, 1312665495, 1283037019, 1254203911, 1226139020, 1198816363, 1172211065, 1146299302, 1121058247, 1096466028, 1072501669, 1049145059, 1026376897, 1004178665, 982532580, 961421565, 940829215, 920739761, 901138046, 882009492, 863340075, 845116298, 827325171, 809954182, 792991280, 776424852, 760243704, 744437045, 728994463, 713905915, 699161709, 684752486, 670669208, 656903147, 643445867, 630289214, 617425306, 604846517, 592545473, 580515036, 568748298, 557238569, 545979371, 534964428, 524187660, 513643172, 503325248, 493228349, 483347097, 473676278, 464210830, 454945840, 445876537, 436998289, 428306595, 419797083, 411465504, 403307727, 395319737, 387497630, 379837606, 372335972, 364989132, 357793587, 350745932, 343842852, 337081117, 330457584, 323969188, 317612948, 311385954, 305285372]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 367).prefactor = (4693386224904391/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 367).cutoff/(generalMeanRows 367).c)).2 =
    (197242608030787/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 367).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 367).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 367).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 367

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 367).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 367).criticalRate j.val*(generalMeanRows 367).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 367).c*(generalMeanRows 367).criticalPoint j.val)).2-
      (generalMeanRows 367).J/2-(generalMeanRows 367).error (generalMeanGrid j.val)+
      (generalMeanRows 367).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 367).c)).2-
      (generalMeanRows 367).J/2-(generalMeanRows 367).error 4 := by
  have he : (generalMeanRows 367).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 367) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 367)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0367

/-! Kernel-checked entropy margins for general spectral rectangle 368. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0368
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5059517353, 4888375743, 4724908317, 4568675415, 4419268500, 4276307439, 4139438085, 4008330103, 3882675026, 3762184501, 3646588708, 3535634929, 3429086251, 3326720387, 3228328603, 3133714739, 3042694314, 2955093706, 2870749404, 2789507314, 2711222128, 2635756735, 2562981686, 2492774697, 2425020184, 2359608839, 2296437238, 2235407470, 2176426803, 2119407362, 2064265837, 2010923210, 1959304502, 1909338531, 1860957692, 1814097750, 1768697646, 1724699317, 1682047525, 1640689696, 1600575777, 1561658093, 1523891216, 1487231843, 1451638683, 1417072344, 1383495236, 1350871471, 1319166779, 1288348418, 1258385094, 1229246891, 1200905197, 1173332637, 1146503010, 1120391232, 1094973279, 1070226132, 1046127730, 1022656922, 999793422, 977517768, 955811280, 934656026, 914034782, 893931003, 874328787, 855212847, 836568484, 818381555, 800638452, 783326075, 766431812, 749943512, 733849469, 718138401, 702799430, 687822065, 673196186, 658912026, 644960158, 631331480, 618017200, 605008823, 592298141, 579877219, 567738382, 555874209, 544277519, 532941364, 521859016, 511023962, 500429894, 490070699, 479940456, 470033424, 460344039, 450866903, 441596782, 432528597, 423657420, 414978465, 406487090, 398178784, 390049165, 382093978, 374309088, 366690475, 359234232, 351936560, 344793765, 337802253, 330958529, 324259190, 317700926, 311280516, 304994822, 298840789, 292815443, 286915885, 281139295]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 368).prefactor = (941956674263761/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 368).cutoff/(generalMeanRows 368).c)).2 =
    (48341654907157/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 368).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 368).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 368).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 368

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 368).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 368).criticalRate j.val*(generalMeanRows 368).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 368).c*(generalMeanRows 368).criticalPoint j.val)).2-
      (generalMeanRows 368).J/2-(generalMeanRows 368).error (generalMeanGrid j.val)+
      (generalMeanRows 368).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 368).c)).2-
      (generalMeanRows 368).J/2-(generalMeanRows 368).error 4 := by
  have he : (generalMeanRows 368).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 368) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 368)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0368

/-! Kernel-checked entropy margins for general spectral rectangle 369. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0369
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5079144126, 4907384114, 4743311180, 4586485952, 4436500117, 4292973712, 4155552705, 4023906829, 3897727643, 3776726781, 3660634374, 3549197624, 3442179511, 3339357615, 3240523047, 3145479474, 3054042223, 2966037467, 2881301475, 2799679925, 2721027269, 2645206150, 2572086868, 2501546879, 2433470338, 2367747676, 2304275201, 2242954738, 2183693287, 2126402706, 2070999424, 2017404161, 1965541675, 1915340528, 1866732863, 1819654194, 1774043215, 1729841622, 1686993937, 1645447355, 1605151595, 1566058757, 1528123195, 1491301393, 1455551850, 1420834972, 1387112969, 1354349763, 1322510894, 1291563436, 1261475920, 1232218256, 1203761665, 1176078608, 1149142727, 1122928786, 1097412610, 1072571039, 1048381871, 1024823821, 1001876472, 979520236, 957736312, 936506649, 915813910, 895641439, 875973229, 856793889, 838088621, 819843188, 802043888, 784677533, 767731424, 751193329, 735051462, 719294463, 703911381, 688891654, 674225092, 659901863, 645912478, 632247770, 618898891, 605857288, 593114699, 580663135, 568494873, 556602443, 544978616, 533616400, 522509024, 511649933, 501032779, 490651412, 480499873, 470572387, 460863354, 451367345, 442079094, 432993493, 424105583, 415410554, 406903734, 398580587, 390436708, 382467818, 374669758, 367038487, 359570079, 352260713, 345106676, 338104356, 331250241, 324540911, 317973040, 311543389, 305248808, 299086227, 293052658, 287145190, 281360987]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 369).prefactor = (942320760483571/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 369).cutoff/(generalMeanRows 369).c)).2 =
    (191911014524899/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 369).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 369).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 369).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 369

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 369).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 369).criticalRate j.val*(generalMeanRows 369).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 369).c*(generalMeanRows 369).criticalPoint j.val)).2-
      (generalMeanRows 369).J/2-(generalMeanRows 369).error (generalMeanGrid j.val)+
      (generalMeanRows 369).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 369).c)).2-
      (generalMeanRows 369).J/2-(generalMeanRows 369).error 4 := by
  have he : (generalMeanRows 369).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 369) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 369)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0369

/-! Kernel-checked entropy margins for general spectral rectangle 370. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0370
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5012012287, 4840109142, 4675928374, 4519028910, 4369000825, 4225462631, 4088058846, 3956457831, 3830349834, 3709445245, 3593473006, 3482179187, 3375325684, 3272689044, 3174059387, 3079239432, 2988043597, 2900297186, 2815835633, 2734503812, 2656155405, 2580652319, 2507864141, 2437667644, 2369946327, 2304589988, 2241494327, 2180560584, 2121695195, 2064809478, 2009819336, 1956644988, 1905210709, 1855444592, 1807278331, 1760647008, 1715488899, 1671745298, 1629360341, 1588280851, 1548456185, 1509838099, 1472380613, 1436039892, 1400774125, 1366543420, 1333309704, 1301036620, 1269689444, 1239234997, 1209641563, 1180878818, 1152917755, 1125730618, 1099290840, 1073572983, 1048552681, 1024206588, 1000512324, 977448434, 954994339, 933130292, 911837344, 891097301, 870892687, 851206716, 832023254, 813326793, 795102418, 777335784, 760013085, 743121033, 726646837, 710578173, 694903170, 679610389, 664688801, 650127770, 635917041, 622046714, 608507239, 595289393, 582384272, 569783274, 557478088, 545460681, 533723288, 522258400, 511058753, 500117321, 489427303, 478982115, 468775385, 458800938, 449052796, 439525163, 430212423, 421109134, 412210015, 403509947, 395003964, 386687247, 378555118, 370603039, 362826602, 355221525, 347783653, 340508944, 333393476, 326433432, 319625107, 312964893, 306449288, 300074879, 293838353, 287736480, 281766123, 275924224, 270207809, 264613982, 259139924]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 370).prefactor = (591025042899193/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 370).cutoff/(generalMeanRows 370).c)).2 =
    (188064841713321/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 370).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 370).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 370).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 370

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 370).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 370).criticalRate j.val*(generalMeanRows 370).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 370).c*(generalMeanRows 370).criticalPoint j.val)).2-
      (generalMeanRows 370).J/2-(generalMeanRows 370).error (generalMeanGrid j.val)+
      (generalMeanRows 370).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 370).c)).2-
      (generalMeanRows 370).J/2-(generalMeanRows 370).error 4 := by
  have he : (generalMeanRows 370).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 370) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 370)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0370

/-! Kernel-checked entropy margins for general spectral rectangle 371. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0371
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4816148248, 4641271628, 4474434595, 4315175976, 4163067143, 4017709177, 3878730340, 3745783807, 3618545635, 3496712931, 3380002200, 3268147853, 3160900850, 3058027471, 2959308190, 2864536660, 2773518770, 2686071796, 2602023610, 2521211964, 2443483826, 2368694764, 2296708391, 2227395836, 2160635269, 2096311452, 2034315330, 1974543640, 1916898566, 1861287400, 1807622236, 1755819688, 1705800617, 1657489886, 1610816126, 1565711519, 1522111595, 1479955043, 1439183532, 1399741544, 1361576223, 1324637221, 1288876566, 1254248534, 1220709524, 1188217947, 1156734117, 1126220156, 1096639893, 1067958776, 1040143792, 1013163387, 986987386, 961586930, 936934408, 913003390, 889768574, 867205726, 845291630, 824004037, 803321620, 783223925, 763691334, 744705023, 726246922, 708299686, 690846654, 673871821, 657359806, 641295826, 625665664, 610455650, 595652628, 581243941, 567217402, 553561280, 540264272, 527315491, 514704446, 502421023, 490455471, 478798384, 467440689, 456373633, 445588766, 435077928, 424833243, 414847101, 405112151, 395621287, 386367643, 377344578, 368545673, 359964716, 351595698, 343432806, 335470409, 327703060, 320125481, 312732563, 305519356, 298481061, 291613030, 284910758, 278369875, 271986145, 265755460, 259673833, 253737399, 247942404, 242285207, 236762271, 231370166, 226105557, 220965207, 215945972, 211044796, 206258713, 201584836, 197020361, 192562565]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 371).prefactor = (4870295257636871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 371).cutoff/(generalMeanRows 371).c)).2 =
    (43973685107257/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 371).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 371).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 371).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 371

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 371).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 371).criticalRate j.val*(generalMeanRows 371).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 371).c*(generalMeanRows 371).criticalPoint j.val)).2-
      (generalMeanRows 371).J/2-(generalMeanRows 371).error (generalMeanGrid j.val)+
      (generalMeanRows 371).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 371).c)).2-
      (generalMeanRows 371).J/2-(generalMeanRows 371).error 4 := by
  have he : (generalMeanRows 371).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 371) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 371)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0371

/-! Kernel-checked entropy margins for general spectral rectangle 372. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0372
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4745165804, 4570609535, 4404112217, 4245211636, 4093478170, 3948511952, 3809940335, 3677415624, 3550613041, 3429228895, 3312978924, 3201596803, 3094832783, 2992452465, 2894235670, 2799975421, 2709477003, 2622557111, 2539043057, 2458772056, 2381590556, 2307353627, 2235924402, 2167173549, 2100978793, 2037224469, 1975801110, 1916605059, 1859538118, 1804507214, 1751424090, 1700205021, 1650770544, 1603045212, 1556957354, 1512438867, 1469425005, 1427854193, 1387667846, 1348810205, 1311228180, 1274871202, 1239691088, 1205641907, 1172679866, 1140763190, 1109852019, 1079908302, 1050895710, 1022779538, 995526628, 969105286, 943485209, 918637412, 894534165, 871148929, 848456296, 826431933, 805052531, 784295754, 764140189, 744565309, 725551421, 707079634, 689131818, 671690567, 654739167, 638261564, 622242331, 606666644, 591520250, 576789441, 562461033, 548522341, 534961156, 521765723, 508924724, 496427257, 484262817, 472421282, 460892893, 449668241, 438738252, 428094172, 417727552, 407630239, 397794363, 388212322, 378876775, 369780629, 360917031, 352279358, 343861204, 335656377, 327658889, 319862945, 312262939, 304853447, 297629216, 290585161, 283716359, 277018040, 270485585, 264114516, 257900495, 251839317, 245926905, 240159306, 234532685, 229043323, 223687614, 218462056, 213363251, 208387902, 203532809, 198794861, 194171042, 189658420, 185254146, 180955456, 176759660]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 372).prefactor = (2439454696807973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 372).cutoff/(generalMeanRows 372).c)).2 =
    (344184881472839/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 372).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 372).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 372).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 372

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 372).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 372).criticalRate j.val*(generalMeanRows 372).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 372).c*(generalMeanRows 372).criticalPoint j.val)).2-
      (generalMeanRows 372).J/2-(generalMeanRows 372).error (generalMeanGrid j.val)+
      (generalMeanRows 372).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 372).c)).2-
      (generalMeanRows 372).J/2-(generalMeanRows 372).error 4 := by
  have he : (generalMeanRows 372).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 372) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 372)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0372

/-! Kernel-checked entropy margins for general spectral rectangle 373. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0373
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5295214303, 5129221835, 4970635666, 4819022852, 4673981504, 4535138080, 4402144962, 4274678281, 4152435976, 4035136031, 3922514895, 3814326046, 3710338690, 3610336581, 3514116941, 3421489480, 3332275496, 3246307056, 3163426238, 3083484444, 3006341756, 2931866358, 2859933989, 2790427446, 2723236124, 2658255587, 2595387174, 2534537631, 2475618774, 2418547169, 2363243843, 2309634004, 2257646796, 2207215051, 2158275079, 2110766452, 2064631819, 2019816722, 1976269428, 1933940772, 1892784014, 1852754692, 1813810502, 1775911174, 1739018353, 1703095503, 1668107797, 1634022030, 1600806526, 1568431060, 1536866777, 1506086117, 1476062751, 1446771513, 1418188338, 1390290207, 1363055093, 1336461906, 1310490450, 1285121374, 1260336130, 1236116935, 1212446727, 1189309137, 1166688448, 1144569567, 1122937993, 1101779789, 1081081553, 1060830395, 1041013913, 1021620166, 1002637658, 984055310, 965862449, 948048784, 930604390, 913519691, 896785444, 880392728, 864332923, 848597702, 833179018, 818069087, 803260383, 788745624, 774517761, 760569969, 746895639, 733488366, 720341944, 707450356, 694807768, 682408518, 670247114, 658318224, 646616671, 635137427, 623875608, 612826466, 601985387, 591347884, 580909593, 570666270, 560613782, 550748110, 541065337, 531561652, 522233342, 513076788, 504088465, 495264936, 486602851, 478098943, 469750024, 461552987, 453504798, 445602496, 437843192, 430224065, 422742360]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 373).prefactor = (2306717983856169/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 373).cutoff/(generalMeanRows 373).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 373).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 373).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 373).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 373

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 373).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 373).criticalRate j.val*(generalMeanRows 373).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 373).c*(generalMeanRows 373).criticalPoint j.val)).2-
      (generalMeanRows 373).J/2-(generalMeanRows 373).error (generalMeanGrid j.val)+
      (generalMeanRows 373).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 373).c)).2-
      (generalMeanRows 373).J/2-(generalMeanRows 373).error 4 := by
  have he : (generalMeanRows 373).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 373) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 373)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0373

/-! Kernel-checked entropy margins for general spectral rectangle 374. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0374
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5304020407, 5137751888, 4978901986, 4827037035, 4681754478, 4542680154, 4409465864, 4281787202, 4159341604, 4041846586, 3929038158, 3820669387, 3716509097, 3616340682, 3519961026, 3427179522, 3337817173, 3251705764, 3168687113, 3088612373, 3011341395, 2936742142, 2864690147, 2795068013, 2727764949, 2662676348, 2599703382, 2538752645, 2479735804, 2422569287, 2367173990, 2313474997, 2261401332, 2210885718, 2161864357, 2114276722, 2068065366, 2023175739, 1979556024, 1937156975, 1895931771, 1855835880, 1816826925, 1778864568, 1741910394, 1705927803, 1670881911, 1636739458, 1603468717, 1571039409, 1539422634, 1508590785, 1478517489, 1449177538, 1420546828, 1392602302, 1365321895, 1338684483, 1312669836, 1287258570, 1262432108, 1238172635, 1214463063, 1191286995, 1168628687, 1146473022, 1124805474, 1103612082, 1082879425, 1062594589, 1042745151, 1023319152, 1004305075, 985691824, 967468708, 949625418, 932152013, 915038902, 898276826, 881856848, 865770335, 850008946, 834564620, 819429561, 804596230, 790057333, 775805808, 761834820, 748137749, 734708179, 721539895, 708626868, 695963254, 683543384, 671361755, 659413027, 647692014, 636193680, 624913132, 613845615, 602986507, 592331314, 581875664, 571615305, 561546100, 551664021, 541965145, 532445656, 523101832, 513930051, 504926780, 496088577, 487412087, 478894036, 470531233, 462320564, 454258990, 446343547, 438571339, 430939541, 423445394]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 374).prefactor = (4621108253272507/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 374).cutoff/(generalMeanRows 374).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 374).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 374).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 374).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 374

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 374).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 374).criticalRate j.val*(generalMeanRows 374).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 374).c*(generalMeanRows 374).criticalPoint j.val)).2-
      (generalMeanRows 374).J/2-(generalMeanRows 374).error (generalMeanGrid j.val)+
      (generalMeanRows 374).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 374).c)).2-
      (generalMeanRows 374).J/2-(generalMeanRows 374).error 4 := by
  have he : (generalMeanRows 374).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 374) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 374)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0374

/-! Kernel-checked entropy margins for general spectral rectangle 375. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0375
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5294722650, 5128760285, 4970209732, 4818637188, 4673639991, 4534843905, 4401900688, 4274485913, 4152297018, 4035051541, 3922485534, 3814352121, 3710420197, 3610473239, 3514308227, 3421734658, 3332573647, 3246657101, 3163826961, 3083934511, 3006839739, 2932410745, 2860523202, 2791059857, 2723910062, 2658969353, 2596139050, 2535325889, 2476441681, 2419402999, 2364130877, 2310550542, 2258591156, 2208185578, 2159270143, 2111784458, 2065671203, 2020875957, 1977347025, 1935035283, 1893894029, 1853878845, 1814947469, 1777059672, 1740177145, 1704263393, 1669283634, 1635204704, 1601994972, 1569624254, 1538063735, 1507285899, 1477264456, 1447974279, 1419391343, 1391492668, 1364256261, 1337661071, 1311686936, 1286314540, 1261525367, 1237301667, 1213626411, 1190483258, 1167856522, 1145731137, 1124092630, 1102927091, 1082221144, 1061961923, 1042137049, 1022734605, 1003743115, 985151523, 966949176, 949125802, 931671493, 914576693, 897832176, 881429035, 865358668, 849612762, 834183283, 819062463, 804242786, 789716984, 775478019, 761519078, 747833560, 734415074, 721257420, 708354592, 695700763, 683290280, 671117658, 659177573, 647464854, 635974480, 624701572, 613641389, 602789320, 592140886, 581691726, 571437599, 561374378, 551498047, 541804693, 532290508, 522951781, 513784897, 504786333, 495952655, 487280514, 478766645, 470407863, 462201062, 454143208, 446231344, 438462580, 430834096, 423343139]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 375).prefactor = (462046279507837/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 375).cutoff/(generalMeanRows 375).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 375).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 375).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 375).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 375

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 375).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 375).criticalRate j.val*(generalMeanRows 375).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 375).c*(generalMeanRows 375).criticalPoint j.val)).2-
      (generalMeanRows 375).J/2-(generalMeanRows 375).error (generalMeanGrid j.val)+
      (generalMeanRows 375).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 375).c)).2-
      (generalMeanRows 375).J/2-(generalMeanRows 375).error 4 := by
  have he : (generalMeanRows 375).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 375) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 375)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0375

/-! Kernel-checked entropy margins for general spectral rectangle 376. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0376
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5303493177, 5137255901, 4978442714, 4826619095, 4681381716, 4542355719, 4409192286, 4281566453, 4159175156, 4041735466, 3928982997, 3820670465, 3716566381, 3616453865, 3520129558, 3427402645, 3338093942, 3252035077, 3169067732, 3089042943, 3011820466, 2937268183, 2865261561, 2795683152, 2728422126, 2663373845, 2600439466, 2539525569, 2480543822, 2423410657, 2368046979, 2314377890, 2262332435, 2211843362, 2162846901, 2115282557, 2069092917, 2024223469, 1980622433, 1938240603, 1897031199, 1856949732, 1817953867, 1780003310, 1743059689, 1707086447, 1672048745, 1637913365, 1604648622, 1572224283, 1540611485, 1509782667, 1479711494, 1450372799, 1421742517, 1393797628, 1366516105, 1339876861, 1313859701, 1288445276, 1263615041, 1239351215, 1215636741, 1192455253, 1169791036, 1147629001, 1125954651, 1104754052, 1084013806, 1063721027, 1043863313, 1024428730, 1005405781, 986783393, 968550894, 950697996, 933214775, 916091658, 899319404, 882889092, 866792105, 851020117, 835565079, 820419212, 805574987, 791025123, 776762572, 762780508, 749072321, 735631607, 722452158, 709527957, 696853167, 684422127, 672229342, 660269478, 648537358, 637027950, 625736369, 614657865, 603787820, 593121747, 582655278, 572384166, 562304276, 552411584, 542702174, 533172229, 523818033, 514635964, 505622494, 496774183, 488087677, 479559706, 471187078, 462966682, 454895481, 446970511, 439188878, 431547758, 424044393]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 376).prefactor = (4628116433623489/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 376).cutoff/(generalMeanRows 376).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 376).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 376).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 376).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 376

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 376).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 376).criticalRate j.val*(generalMeanRows 376).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 376).c*(generalMeanRows 376).criticalPoint j.val)).2-
      (generalMeanRows 376).J/2-(generalMeanRows 376).error (generalMeanGrid j.val)+
      (generalMeanRows 376).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 376).c)).2-
      (generalMeanRows 376).J/2-(generalMeanRows 376).error 4 := by
  have he : (generalMeanRows 376).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 376) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 376)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0376

/-! Kernel-checked entropy margins for general spectral rectangle 377. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0377
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5312841156, 5146296127, 4987182053, 4835064545, 4689540380, 4550234770, 4416798941, 4288907946, 4166258717, 4048568301, 3935572269, 3827023277, 3722689766, 3622354767, 3525814829, 3432879027, 3343368065, 3257113451, 3173956737, 3093748830, 3016349348, 2941626034, 2869454215, 2799716297, 2732301306, 2667104460, 2604026769, 2542974668, 2483859681, 2426598095, 2371110673, 2317322377, 2265162111, 2214562488, 2165459603, 2117792829, 2071504622, 2026540343, 1982848087, 1940378527, 1899084764, 1858922192, 1819848364, 1781822875, 1744807245, 1708764813, 1673660639, 1639461406, 1606135334, 1573652096, 1541982741, 1511099617, 1480976309, 1451587565, 1422909241, 1394918243, 1367592467, 1340910757, 1314852846, 1289399321, 1264531571, 1240231754, 1216482753, 1193268141, 1170572152, 1148379642, 1126676060, 1105447423, 1084680286, 1064361716, 1044479268, 1025020963, 1005975265, 987331060, 969077638, 951204675, 933702211, 916560640, 899770688, 883323403, 867210138, 851422537, 835952527, 820792298, 805934298, 791371222, 777095997, 763101775, 749381925, 735930022, 722739838, 709805336, 697120663, 684680138, 672478250, 660509651, 648769146, 637251690, 625952382, 614866459, 603989292, 593316379, 582843341, 572565919, 562479968, 552581455, 542866450, 533331129, 523971766, 514784732, 505766488, 496913588, 488222668, 479690452, 471313741, 463089417, 455014437, 447085830, 439300697, 431656207, 424149597]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 377).prefactor = (57859916225987/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 377).cutoff/(generalMeanRows 377).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 377).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 377).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 377).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 377

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 377).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 377).criticalRate j.val*(generalMeanRows 377).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 377).c*(generalMeanRows 377).criticalPoint j.val)).2-
      (generalMeanRows 377).J/2-(generalMeanRows 377).error (generalMeanGrid j.val)+
      (generalMeanRows 377).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 377).c)).2-
      (generalMeanRows 377).J/2-(generalMeanRows 377).error 4 := by
  have he : (generalMeanRows 377).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 377) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 377)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0377

/-! Kernel-checked entropy margins for general spectral rectangle 378. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0378
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5321676574, 5154854575, 4995475889, 4843105406, 4697339229, 4557801950, 4424144213, 4296040531, 4173187333, 4055301194, 3942117246, 3833387735, 3728880713, 3628378854, 3531678367, 3438588010, 3348928189, 3262530130, 3179235125, 3098893829, 3021365629, 2946518048, 2874226205, 2804372311, 2736845207, 2671539937, 2608357345, 2547203713, 2487990415, 2430633602, 2375053903, 2321176155, 2268929145, 2218245374, 2169060829, 2121314783, 2074949597, 2029910541, 1986145624, 1943605436, 1902243000, 1862013636, 1822874828, 1784786101, 1747708913, 1711606541, 1676443988, 1642187881, 1608806387, 1576269128, 1544547105, 1513612622, 1483439218, 1454001600, 1425275583, 1397238035, 1369866816, 1343140732, 1317039487, 1291543631, 1266634526, 1242294298, 1218505801, 1195252583, 1172518850, 1150289432, 1128549757, 1107285816, 1086484143, 1066131782, 1046216270, 1026725605, 1007648233, 988973022, 970689244, 952786557, 935254986, 918084908, 901267034, 884792397, 868652335, 852838479, 837342741, 822157300, 807274592, 792687297, 778388331, 764370837, 750628170, 737153896, 723941776, 710985764, 698279996, 685818782, 673596602, 661608099, 649848069, 638311459, 626993360, 615889001, 604993745, 594303082, 583812627, 573518114, 563415390, 553500415, 543769253, 534218075, 524843148, 515640835, 506607594, 497739970, 489034597, 480488191, 472097550, 463859549, 455771140, 447829347, 440031267, 432374064, 424854970]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 378).prefactor = (4636491123350709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 378).cutoff/(generalMeanRows 378).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 378).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 378).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 378).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 378

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 378).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 378).criticalRate j.val*(generalMeanRows 378).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 378).c*(generalMeanRows 378).criticalPoint j.val)).2-
      (generalMeanRows 378).J/2-(generalMeanRows 378).error (generalMeanGrid j.val)+
      (generalMeanRows 378).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 378).c)).2-
      (generalMeanRows 378).J/2-(generalMeanRows 378).error 4 := by
  have he : (generalMeanRows 378).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 378) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 378)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0378

/-! Kernel-checked entropy margins for general spectral rectangle 379. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0379
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5247694276, 5080508407, 4920789761, 4768103523, 4622045996, 4482241879, 4348341845, 4220020367, 4096973764, 3978918446, 3865589327, 3756738387, 3652133375, 3551556619, 3454803954, 3361683736, 3272015942, 3185631351, 3102370786, 3022084422, 2944631150, 2869877989, 2797699543, 2727977507, 2660600197, 2595462131, 2532463628, 2471510441, 2412513418, 2355388188, 2300054860, 2246437757, 2194465155, 2144069048, 2095184928, 2047751577, 2001710871, 1957007603, 1913589317, 1871406142, 1830410653, 1790557726, 1751804413, 1714109818, 1677434983, 1641742784, 1606997826, 1573166352, 1540216154, 1508116488, 1476837999, 1446352642, 1416633619, 1387655308, 1359393207, 1331823870, 1304924858, 1278674685, 1253052767, 1228039383, 1203615626, 1179763362, 1156465197, 1133704435, 1111465046, 1089731634, 1068489406, 1047724142, 1027422169, 1007570334, 988155980, 969166923, 950591429, 932418194, 914636324, 897235317, 880205045, 863535735, 847217957, 831242606, 815600887, 800284307, 785284653, 770593989, 756204638, 742109172, 728300406, 714771381, 701515360, 688525817, 675796427, 663321062, 651093777, 639108809, 627360566, 615843621, 604552705, 593482705, 582628653, 571985721, 561549219, 551314589, 541277397, 531433333, 521778202, 512307924, 503018528, 493906148, 484967018, 476197474, 467593942, 459152943, 450871086, 442745065, 434771657, 426947718, 419270184, 411736064, 404342440, 397086465, 389965359]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 379).prefactor = (115947251363031/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 379).cutoff/(generalMeanRows 379).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 379).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 379).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 379).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 379

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 379).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 379).criticalRate j.val*(generalMeanRows 379).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 379).c*(generalMeanRows 379).criticalPoint j.val)).2-
      (generalMeanRows 379).J/2-(generalMeanRows 379).error (generalMeanGrid j.val)+
      (generalMeanRows 379).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 379).c)).2-
      (generalMeanRows 379).J/2-(generalMeanRows 379).error 4 := by
  have he : (generalMeanRows 379).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 379) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 379)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0379

/-! Kernel-checked entropy margins for general spectral rectangle 380. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0380
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5265302337, 5097555494, 4937300929, 4784102370, 4637554763, 4497281548, 4362932228, 4234180181, 4110720709, 3992269269, 3878559886, 3769343709, 3664387706, 3563473476, 3466396169, 3372963496, 3282994832, 3196320387, 3112780450, 3032224694, 2954511536, 2879507548, 2807086916, 2737130935, 2669527548, 2604170919, 2540961031, 2479803322, 2420608342, 2363291434, 2307772441, 2253975432, 2201828441, 2151263236, 2102215091, 2054622582, 2008427391, 1963574127, 1920010155, 1877685440, 1836552395, 1796565746, 1757682400, 1719861325, 1683063432, 1647251471, 1612389930, 1578444938, 1545384179, 1513176807, 1481793366, 1451205719, 1421386977, 1392311433, 1363954501, 1336292659, 1309303390, 1282965137, 1257257248, 1232159934, 1207654226, 1183721928, 1160345589, 1137508455, 1115194444, 1093388108, 1072074604, 1051239665, 1030869571, 1010951126, 991471629, 972418856, 953781034, 935546820, 917705286, 900245892, 883158476, 866433234, 850060704, 834031749, 818337546, 802969573, 787919590, 773179633, 758741999, 744599238, 730744138, 717169718, 703869218, 690836090, 678063988, 665546763, 653278451, 641253269, 629465605, 617910016, 606581215, 595474071, 584583599, 573904956, 563433436, 553164464, 543093594, 533216499, 523528971, 514026917, 504706352, 495563396, 486594272, 477795302, 469162902, 460693580, 452383934, 444230647, 436230485, 428380294, 420676999, 413117599, 405699167, 398418845, 391273845]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 380).prefactor = (4653451984262199/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 380).cutoff/(generalMeanRows 380).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 380).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 380).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 380).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 380

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 380).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 380).criticalRate j.val*(generalMeanRows 380).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 380).c*(generalMeanRows 380).criticalPoint j.val)).2-
      (generalMeanRows 380).J/2-(generalMeanRows 380).error (generalMeanGrid j.val)+
      (generalMeanRows 380).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 380).c)).2-
      (generalMeanRows 380).J/2-(generalMeanRows 380).error 4 := by
  have he : (generalMeanRows 380).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 380) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 380)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0380

/-! Kernel-checked entropy margins for general spectral rectangle 381. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0381
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5312278232, 5145765589, 4986689335, 4834614225, 4689136264, 4549879976, 4416495962, 4288658721, 4166064687, 4048430462, 3935491223, 3826999275, 3722722746, 3622444397, 3525960532, 3433080020, 3343623380, 3257421962, 3174317184, 3094159837, 3016809444, 2942133667, 2870007769, 2800314105, 2732941664, 2667785633, 2604747005, 2543732206, 2484652758, 2427424954, 2371969568, 2318211578, 2266079911, 2215507205, 2166429582, 2118786450, 2072520298, 2027576526, 1983903266, 1941451232, 1900173567, 1860025705, 1820965246, 1782951825, 1745947008, 1709914178, 1674818437, 1640626512, 1607306667, 1574828618, 1543163455, 1512283570, 1482162586, 1452775292, 1424097584, 1396106406, 1368779692, 1342096321, 1316036064, 1290579541, 1265708176, 1241404158, 1217650402, 1194430514, 1171728755, 1149530010, 1127819757, 1106584040, 1085809438, 1065483044, 1045592437, 1026125661, 1007071201, 988417966, 970155266, 952272795, 934760613, 917609132, 900809096, 884351568, 868227917, 852429803, 836949164, 821778208, 806909394, 792335430, 778049253, 764044028, 750313134, 736850156, 723648876, 710703266, 698007481, 685555849, 673342867, 661363192, 649611638, 638083165, 626772880, 615676024, 604787974, 594104233, 583620427, 573332300, 563235713, 553326635, 543601141, 534055410, 524685719, 515488441, 506460041, 497597073, 488896178, 480354080, 471967583, 463733570, 455649000, 447710902, 439916380, 432262602, 424746808]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 381).prefactor = (4635782750159009/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 381).cutoff/(generalMeanRows 381).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 381).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 381).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 381).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 381

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 381).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 381).criticalRate j.val*(generalMeanRows 381).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 381).c*(generalMeanRows 381).criticalPoint j.val)).2-
      (generalMeanRows 381).J/2-(generalMeanRows 381).error (generalMeanGrid j.val)+
      (generalMeanRows 381).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 381).c)).2-
      (generalMeanRows 381).J/2-(generalMeanRows 381).error 4 := by
  have he : (generalMeanRows 381).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 381) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 381)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0381

/-! Kernel-checked entropy margins for general spectral rectangle 382. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0382
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5321077839, 5154289374, 4994949615, 4842622598, 4696903658, 4557416696, 4423811736, 4295762738, 4172965631, 4055136549, 3942010229, 3833338568, 3728889309, 3628444852, 3531801165, 3438766799, 3349161978, 3262817770, 3179575332, 3099285207, 3021806685, 2947007211, 2874761839, 2804952730, 2737468688, 2672204728, 2609061679, 2547945812, 2488768500, 2431445900, 2375898654, 2322051616, 2269833595, 2219177117, 2170018199, 2122296147, 2075953357, 2030935137, 1987189534, 1944667179, 1903321139, 1863106774, 1823981612, 1785905224, 1748839109, 1712746592, 1677592716, 1643344154, 1609969116, 1577437268, 1545719653, 1514788616, 1484617737, 1455181765, 1426456553, 1398419008, 1371047029, 1344319458, 1318216033, 1292717342, 1267804778, 1243460501, 1219667398, 1196409047, 1173669683, 1151434167, 1129687952, 1108417058, 1087608044, 1067247980, 1047324425, 1027825403, 1008739380, 990055246, 971762295, 953850202, 936309012, 919129121, 902301256, 885816466, 869666107, 853841823, 838335542, 823139455, 808246012, 793647906, 779338065, 765309641, 751556002, 738070723, 724847575, 711880522, 699163706, 686691449, 674458236, 662458717, 650687697, 639140128, 627811108, 616695871, 605789785, 595088346, 584587174, 574282006, 564168694, 554243202, 544501598, 534940055, 525554843, 516342330, 507298974, 498421325, 489706018, 481149770, 472749381, 464501729, 456403767, 448452520, 440645086, 432978631, 425450386]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 382).prefactor = (1160865441421399/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 382).cutoff/(generalMeanRows 382).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 382).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 382).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 382).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 382

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 382).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 382).criticalRate j.val*(generalMeanRows 382).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 382).c*(generalMeanRows 382).criticalPoint j.val)).2-
      (generalMeanRows 382).J/2-(generalMeanRows 382).error (generalMeanGrid j.val)+
      (generalMeanRows 382).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 382).c)).2-
      (generalMeanRows 382).J/2-(generalMeanRows 382).error 4 := by
  have he : (generalMeanRows 382).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 382) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 382)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0382

/-! Kernel-checked entropy margins for general spectral rectangle 383. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0383
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5237641978, 5070793689, 4911411407, 4759059321, 4613332855, 4473855940, 4340278579, 4212274663, 4089540011, 3971790606, 3858761003, 3750202884, 3645883750, 3545585737, 3449104527, 3356248365, 3266837152, 3180701625, 3097682591, 3017630237, 2940403487, 2865869413, 2793902693, 2724385106, 2657205071, 2592257216, 2529441984, 2468665260, 2409838030, 2352876066, 2297699629, 2244233194, 2192405194, 2142147782, 2093396612, 2046090624, 2000171858, 1955585269, 1912278560, 1870202020, 1829308382, 1789552679, 1750892116, 1713285950, 1676695372, 1641083403, 1606414793, 1572655926, 1539774731, 1507740598, 1476524302, 1446097927, 1416434800, 1387509418, 1359297397, 1331775407, 1304921117, 1278713149, 1253131026, 1228155124, 1203766635, 1179947520, 1156680475, 1133948892, 1111736828, 1090028969, 1068810599, 1048067575, 1027786299, 1007953687, 988557152, 969584575, 951024285, 932865039, 915096001, 897706726, 880687139, 864027519, 847718486, 831750982, 816116259, 800805866, 785811635, 771125667, 756740325, 742648218, 728842196, 715315334, 702060928, 689072482, 676343701, 663868484, 651640915, 639655256, 627905939, 616387561, 605094876, 594022792, 583166359, 572520772, 562081359, 551843578, 541803012, 531955368, 522296466, 512822239, 503528732, 494412089, 485468560, 476694490, 468086317, 459640574, 451353878, 443222933, 435244526, 427415521, 419732862, 412193566, 404794721, 397533488, 390407093]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 383).prefactor = (4644201750342073/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 383).cutoff/(generalMeanRows 383).c)).2 =
    (217877939319293/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 383).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 383).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 383).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 383

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 383).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 383).criticalRate j.val*(generalMeanRows 383).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 383).c*(generalMeanRows 383).criticalPoint j.val)).2-
      (generalMeanRows 383).J/2-(generalMeanRows 383).error (generalMeanGrid j.val)+
      (generalMeanRows 383).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 383).c)).2-
      (generalMeanRows 383).J/2-(generalMeanRows 383).error 4 := by
  have he : (generalMeanRows 383).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 383) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 383)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0383

/-! Kernel-checked entropy margins for general spectral rectangle 384. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0384
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5246352338, 5079226574, 4919579235, 4766973782, 4621004969, 4481296100, 4347496596, 4219279805, 4096341041, 3978395816, 3865178241, 3756439586, 3651946967, 3551482155, 3454840494, 3361829909, 3272270003, 3185991229, 3102834132, 3022648649, 2945293468, 2870635442, 2798549039, 2728915842, 2661624084, 2596568220, 2533648524, 2472770726, 2413845665, 2356788971, 2301520774, 2247965422, 2196051231, 2145710240, 2096877994, 2049493335, 2003498205, 1958837467, 1915458738, 1873312224, 1832350578, 1792528760, 1753803904, 1716135197, 1679483767, 1643812575, 1609086310, 1575271301, 1542335423, 1510248016, 1478979807, 1448502833, 1418790374, 1389816889, 1361557951, 1333990190, 1307091241, 1280839688, 1255215021, 1230197584, 1205768535, 1181909809, 1158604070, 1135834684, 1113585681, 1091841720, 1070588063, 1049810544, 1029495539, 1009629945, 990201153, 971197024, 952605867, 934416422, 916617834, 899199640, 882151748, 865464423, 849128268, 833134209, 817473486, 802137631, 787118464, 772408073, 757998807, 743883265, 730054283, 716504926, 703228477, 690218430, 677468481, 664972518, 652724614, 640719022, 628950166, 617412632, 606101168, 595010670, 584136183, 573472892, 563016118, 552761311, 542704047, 532840026, 523165061, 513675079, 504366115, 495234312, 486275909, 477487247, 468864759, 460404970, 452104493, 443960027, 435968351, 428126327, 420430891, 412879056, 405467907, 398194598, 391056352]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 384).prefactor = (1162981300085671/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 384).cutoff/(generalMeanRows 384).c)).2 =
    (217877939319293/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 384).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 384).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 384).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 384

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 384).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 384).criticalRate j.val*(generalMeanRows 384).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 384).c*(generalMeanRows 384).criticalPoint j.val)).2-
      (generalMeanRows 384).J/2-(generalMeanRows 384).error (generalMeanGrid j.val)+
      (generalMeanRows 384).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 384).c)).2-
      (generalMeanRows 384).J/2-(generalMeanRows 384).error 4 := by
  have he : (generalMeanRows 384).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 384) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 384)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0384

/-! Kernel-checked entropy margins for general spectral rectangle 385. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0385
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5263816537, 5096134441, 4935955663, 4782842214, 4636387495, 4496213559, 4361968660, 4233325058, 4109977052, 3991639207, 3878044751, 3768944124, 3664103667, 3563304425, 3466341060, 3373020859, 3283162824, 3196596843, 3113162930, 3032710523, 2955097841, 2880191291, 2807864924, 2737999930, 2670484170, 2605211746, 2542082602, 2481002152, 2421880939, 2364634314, 2309182139, 2255448510, 2203361505, 2152852938, 2103858139, 2056315744, 2010167504, 1965358099, 1921834968, 1879548156, 1838450156, 1798495778, 1759642013, 1721847914, 1685074478, 1649284543, 1614442680, 1580515107, 1547469591, 1515275371, 1483903075, 1453324648, 1423513282, 1394443349, 1366090342, 1338430813, 1311442322, 1285103382, 1259393415, 1234292699, 1209782330, 1185844182, 1162460862, 1139615681, 1117292615, 1095476272, 1074151866, 1053305181, 1032922552, 1012990829, 993497362, 974429971, 955776927, 937526932, 919669096, 902192920, 885088279, 868345405, 851954869, 835907569, 820194714, 804807809, 789738645, 774979286, 760522054, 746359524, 732484507, 718890047, 705569403, 692516048, 679723656, 667186096, 654897421, 642851865, 631043832, 619467892, 608118774, 596991357, 586080671, 575381884, 564890301, 554601357, 544510615, 534613758, 524906587, 515385014, 506045063, 496882861, 487894638, 479076720, 470425529, 461937579, 453609471, 445437893, 437419614, 429551485, 421830433, 414253459, 406817639, 399520119, 392358111]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 385).prefactor = (2333705327353693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 385).cutoff/(generalMeanRows 385).c)).2 =
    (217877939319293/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 385).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 385).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 385).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 385

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 385).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 385).criticalRate j.val*(generalMeanRows 385).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 385).c*(generalMeanRows 385).criticalPoint j.val)).2-
      (generalMeanRows 385).J/2-(generalMeanRows 385).error (generalMeanGrid j.val)+
      (generalMeanRows 385).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 385).c)).2-
      (generalMeanRows 385).J/2-(generalMeanRows 385).error 4 := by
  have he : (generalMeanRows 385).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 385) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 385)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0385

/-! Kernel-checked entropy margins for general spectral rectangle 386. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0386
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5282969480, 5114659780, 4953867499, 4800154899, 4653115567, 4512371682, 4377571567, 4248387507, 4124513780, 4005664889, 3891573967, 3781991327, 3676683156, 3575430319, 3478027280, 3384281104, 3294010560, 3207045288, 3123225042, 3042398990, 2964425074, 2889169419, 2816505787, 2746315077, 2678484854, 2612908928, 2549486946, 2488124029, 2428730427, 2371221198, 2315515918, 2261538398, 2209216434, 2158481563, 2109268842, 2061516642, 2015166448, 1970162684, 1926452538, 1883985807, 1842714744, 1802593924, 1763580110, 1725632130, 1688710766, 1652778642, 1617800127, 1583741237, 1550569546, 1518254105, 1486765361, 1456075080, 1426156285, 1396983181, 1368531101, 1340776442, 1313696614, 1287269985, 1261475836, 1236294311, 1211706376, 1187693777, 1164239001, 1141325239, 1118936357, 1097056852, 1075671833, 1054766984, 1034328541, 1014343261, 994798403, 975681700, 956981341, 938685945, 920784545, 903266568, 886121817, 869340456, 852912989, 836830251, 821083388, 805663849, 790563367, 775773952, 761287875, 747097659, 733196069, 719576102, 706230973, 693154114, 680339157, 667779932, 655470455, 643404923, 631577708, 619983345, 608616532, 597472119, 586545105, 575830631, 565323974, 555020547, 544915885, 535005648, 525285615, 515751678, 506399838, 497226204, 488226985, 479398491, 470737126, 462239387, 453901859, 445721214, 437694209, 429817677, 422088535, 414503770, 407060446, 399755696, 392586721]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 386).prefactor = (186762645213841/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 386).cutoff/(generalMeanRows 386).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 386).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 386).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 386).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 386

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 386).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 386).criticalRate j.val*(generalMeanRows 386).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 386).c*(generalMeanRows 386).criticalPoint j.val)).2-
      (generalMeanRows 386).J/2-(generalMeanRows 386).error (generalMeanGrid j.val)+
      (generalMeanRows 386).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 386).c)).2-
      (generalMeanRows 386).J/2-(generalMeanRows 386).error 4 := by
  have he : (generalMeanRows 386).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 386) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 386)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0386

/-! Kernel-checked entropy margins for general spectral rectangle 387. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0387
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5209020101, 5040442899, 4879418363, 4725507273, 4578301810, 4437422817, 4302517348, 4173256476, 4049333325, 3930461295, 3816372462, 3706816130, 3601557515, 3500376553, 3403066812, 3309434501, 3219297560, 3132484835, 3048835311, 2968197416, 2890428380, 2815393638, 2742966288, 2673026584, 2605461473, 2540164162, 2477033719, 2415974703, 2356896818, 2299714598, 2244347108, 2190717666, 2138753590, 2088385955, 2039549369, 1992181768, 1946224216, 1901620730, 1858318103, 1816265747, 1775415547, 1735721716, 1697140669, 1659630896, 1623152853, 1587668846, 1553142938, 1519540845, 1486829855, 1454978740, 1423957674, 1393738164, 1364292978, 1335596076, 1307622553, 1280348577, 1253751334, 1227808979, 1202500583, 1177806088, 1153706267, 1130182677, 1107217622, 1084794121, 1062895865, 1041507191, 1020613048, 1000198968, 980251038, 960755874, 941700598, 923072811, 904860573, 887052381, 869637151, 852604195, 835943207, 819644245, 803697713, 788094348, 772825203, 757881637, 743255298, 728938112, 714922273, 701200227, 687764667, 674608521, 661724938, 649107286, 636749138, 624644266, 612786632, 601170381, 589789835, 578639482, 567713977, 557008126, 546516890, 536235372, 526158815, 516282595, 506602219, 497113319, 487811643, 478693060, 469753548, 460989192, 452396182, 443970810, 435709463, 427608621, 419664857, 411874831, 404235287, 396743051, 389395028, 382188201, 375119627, 368186435, 361385822]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 387).prefactor = (2342366333989457/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 387).cutoff/(generalMeanRows 387).c)).2 =
    (424856363912193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 387).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 387).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 387).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 387

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 387).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 387).criticalRate j.val*(generalMeanRows 387).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 387).c*(generalMeanRows 387).criticalPoint j.val)).2-
      (generalMeanRows 387).J/2-(generalMeanRows 387).error (generalMeanGrid j.val)+
      (generalMeanRows 387).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 387).c)).2-
      (generalMeanRows 387).J/2-(generalMeanRows 387).error 4 := by
  have he : (generalMeanRows 387).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 387) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 387)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0387

/-! Kernel-checked entropy margins for general spectral rectangle 388. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0388
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5284329123, 5115963587, 4955103899, 4801314059, 4654189223, 4513352982, 4378454929, 4249168489, 4125188962, 4006231765, 3892030848, 3782337250, 3676917803, 3575553945, 3478040641, 3384185401, 3293807380, 3206736555, 3122812968, 3041886038, 2963813915, 2888462902, 2815706908, 2745426947, 2677510680, 2611851985, 2548350560, 2486911558, 2427445245, 2369866681, 2314095428, 2260055277, 2207673990, 2156883062, 2107617503, 2059815625, 2013418854, 1968371546, 1924620820, 1882116397, 1840810456, 1800657492, 1761614186, 1723639286, 1686693490, 1650739340, 1615741120, 1581664765, 1548477765, 1516149088, 1484649101, 1453949490, 1424023197, 1394844352, 1366388210, 1338631094, 1311550340, 1285124246, 1259332021, 1234153743, 1209570312, 1185563408, 1162115457, 1139209592, 1116829615, 1094959971, 1073585711, 1052692469, 1032266427, 1012294295, 992763283, 973661079, 954975827, 936696105, 918810905, 901309614, 884181999, 867418186, 851008647, 834944182, 819215907, 803815240, 788733885, 773963825, 759497305, 745326823, 731445120, 717845169, 704520167, 691463521, 678668846, 666129953, 653840842, 641795692, 629988859, 618414864, 607068390, 595944274, 585037504, 574343207, 563856652, 553573237, 543488492, 533598066, 523897729, 514383365, 505050968, 495896640, 486916584, 478107104, 469464597, 460985557, 452666563, 444504284, 436495472, 428636957, 420925652, 413358542, 405932688, 398645221, 391493340]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 388).prefactor = (2327478420157369/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 388).cutoff/(generalMeanRows 388).c)).2 =
    (214919350805249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 388).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 388).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 388).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 388

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 388).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 388).criticalRate j.val*(generalMeanRows 388).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 388).c*(generalMeanRows 388).criticalPoint j.val)).2-
      (generalMeanRows 388).J/2-(generalMeanRows 388).error (generalMeanGrid j.val)+
      (generalMeanRows 388).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 388).c)).2-
      (generalMeanRows 388).J/2-(generalMeanRows 388).error 4 := by
  have he : (generalMeanRows 388).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 388) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 388)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0388

/-! Kernel-checked entropy margins for general spectral rectangle 389. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0389
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5210724672, 5042088220, 4880992976, 4727001448, 4579707379, 4438733013, 4303726667, 4174360548, 4050328795, 3931345718, 3817144202, 3707474272, 3602101788, 3500807251, 3403384731, 3309640874, 3219394005, 3132473303, 3048718039, 2967976891, 2890107293, 2814974858, 2742452827, 2672421571, 2604768128, 2539385773, 2476173625, 2415036271, 2355883434, 2298629646, 2243193960, 2189499672, 2137474065, 2087048173, 2038156555, 1990737089, 1944730779, 1900081575, 1856736199, 1814643990, 1773756755, 1734028629, 1695415945, 1657877113, 1621372505, 1585864346, 1551316612, 1517694939, 1484966532, 1453100080, 1422065676, 1391834748, 1362379984, 1333675267, 1305695616, 1278417124, 1251816905, 1225873041, 1200564535, 1175871262, 1151773927, 1128254024, 1105293796, 1082876199, 1060984869, 1039604084, 1018718740, 998314314, 978376845, 958892898, 939849548, 921234351, 903035322, 885240916, 867840009, 850821875, 834176169, 817892914, 801962479, 786375569, 771123206, 756196718, 741587724, 727288124, 713290084, 699586027, 686168622, 673030773, 660165609, 647566477, 635226930, 623140722, 611301798, 599704287, 588342493, 577210893, 566304124, 555616981, 545144412, 534881509, 524823502, 514965759, 505303777, 495833176, 486549700, 477449207, 468527667, 459781160, 451205870, 442798081, 434554174, 426470628, 418544007, 410770969, 403148253, 395672681, 388341157, 381150660, 374098243, 367181033, 360396227]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 389).prefactor = (2335350664318451/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 389).cutoff/(generalMeanRows 389).c)).2 =
    (10547553800369/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 389).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 389).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 389).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 389

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 389).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 389).criticalRate j.val*(generalMeanRows 389).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 389).c*(generalMeanRows 389).criticalPoint j.val)).2-
      (generalMeanRows 389).J/2-(generalMeanRows 389).error (generalMeanGrid j.val)+
      (generalMeanRows 389).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 389).c)).2-
      (generalMeanRows 389).J/2-(generalMeanRows 389).error 4 := by
  have he : (generalMeanRows 389).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 389) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 389)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0389

/-! Kernel-checked entropy margins for general spectral rectangle 390. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0390
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5229928663, 5060671540, 4898969140, 4744384247, 4596510810, 4454971224, 4319413900, 4189511090, 4064956937, 3945465710, 3830770223, 3720620397, 3614781956, 3513035245, 3415174153, 3321005127, 3230346279, 3143026554, 3058884985, 2977769994, 2899538758, 2824056619, 2751196547, 2680838635, 2612869642, 2547182562, 2483676228, 2422254947, 2362828159, 2305310117, 2249619596, 2195679614, 2143417185, 2092763072, 2043651569, 1996020296, 1949810001, 1904964381, 1861429913, 1819155695, 1778093300, 1738196631, 1699421798, 1661726992, 1625072371, 1589419952, 1554733509, 1520978483, 1488121886, 1456132222, 1424979405, 1394634687, 1365070586, 1336260823, 1308180257, 1280804827, 1254111498, 1228078209, 1202683822, 1177908078, 1153731551, 1130135611, 1107102379, 1084614694, 1062656078, 1041210701, 1020263352, 999799409, 979804811, 960266032, 941170052, 922504342, 904256834, 886415900, 868970338, 851909348, 835222512, 818899784, 802931466, 787308199, 772020942, 757060966, 742419831, 728089383, 714061734, 700329259, 686884576, 673720543, 660830245, 648206985, 635844275, 623735830, 611875556, 600257545, 588876067, 577725565, 566800644, 556096068, 545606755, 535327768, 525254312, 515381726, 505705483, 496221180, 486924537, 477811389, 468877686, 460119488, 451532957, 443114362, 434860064, 426766524, 418830293, 411048009, 403416398, 395932269, 388592509, 381394086, 374334040, 367409486, 360617608]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 390).prefactor = (2336158287255847/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 390).cutoff/(generalMeanRows 390).c)).2 =
    (209478320892503/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 390).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 390).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 390).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 390

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 390).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 390).criticalRate j.val*(generalMeanRows 390).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 390).c*(generalMeanRows 390).criticalPoint j.val)).2-
      (generalMeanRows 390).J/2-(generalMeanRows 390).error (generalMeanGrid j.val)+
      (generalMeanRows 390).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 390).c)).2-
      (generalMeanRows 390).J/2-(generalMeanRows 390).error 4 := by
  have he : (generalMeanRows 390).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 390) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 390)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0390

/-! Kernel-checked entropy margins for general spectral rectangle 391. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0391
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5157909944, 4988417295, 4826514725, 4671763470, 4523756018, 4382113375, 4246482633, 4116534787, 3991962781, 3872479742, 3757817390, 3647724602, 3541966099, 3440321267, 3342583073, 3248557081, 3158060550, 3070921610, 2986978506, 2906078901, 2828079243, 2752844170, 2680245972, 2610164088, 2542484643, 2477100022, 2413908469, 2352813720, 2293724665, 2236555024, 2181223057, 2127651287, 2075766244, 2025498227, 1976781081, 1929551989, 1883751277, 1839322235, 1796210946, 1754366126, 1713738978, 1674283050, 1635954104, 1598709997, 1562510563, 1527317506, 1493094300, 1459806089, 1427419604, 1395903074, 1365226149, 1335359825, 1306276373, 1277949274, 1250353155, 1223463733, 1197257757, 1171712957, 1146807995, 1122522418, 1098836613, 1075731768, 1053189830, 1031193470, 1009726048, 988771578, 968314700, 948340645, 928835213, 909784744, 891176090, 872996596, 855234076, 837876787, 820913417, 804333060, 788125197, 772279685, 756786733, 741636892, 726821038, 712330356, 698156332, 684290736, 670725610, 657453259, 644466238, 631757344, 619319602, 607146260, 595230779, 583566822, 572148248, 560969106, 550023624, 539306202, 528811411, 518533980, 508468793, 498610883, 488955425, 479497735, 470233258, 461157569, 452266369, 443555472, 435020813, 426658435, 418464486, 410435222, 402566995, 394856255, 387299545, 379893497, 372634832, 365520353, 358546946, 351711576, 345011283, 338443182, 332004460]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 391).prefactor = (937649445461797/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 391).cutoff/(generalMeanRows 391).c)).2 =
    (411082585354099/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 391).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 391).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 391).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 391

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 391).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 391).criticalRate j.val*(generalMeanRows 391).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 391).c*(generalMeanRows 391).criticalPoint j.val)).2-
      (generalMeanRows 391).J/2-(generalMeanRows 391).error (generalMeanGrid j.val)+
      (generalMeanRows 391).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 391).c)).2-
      (generalMeanRows 391).J/2-(generalMeanRows 391).error 4 := by
  have he : (generalMeanRows 391).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 391) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 391)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0391

/-! Kernel-checked entropy margins for general spectral rectangle 392. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0392
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5228348937, 5059142105, 4897501988, 4742989614, 4595197350, 4453746166, 4318283187, 4188479513, 4064028247, 3944642732, 3830054951, 3720014085, 3614285198, 3512648053, 3414896020, 3320835092, 3230282981, 3143068286, 3059029737, 2978015497, 2899882521, 2824495965, 2751728642, 2681460518, 2613578250, 2547974753, 2484548801, 2423204663, 2363851752, 2306404314, 2250781128, 2196905230, 2144703657, 2094107209, 2045050224, 1997470371, 1951308454, 1906508233, 1863016249, 1820781671, 1779756143, 1739893644, 1701150360, 1663484561, 1626856483, 1591228224, 1556563639, 1522828248, 1489989143, 1458014909, 1426875537, 1396542359, 1366987970, 1338186165, 1310111878, 1282741122, 1256050932, 1230019319, 1204625212, 1179848418, 1155669579, 1132070124, 1109032238, 1086538818, 1064573444, 1043120343, 1022164358, 1001690919, 981686015, 962136167, 943028407, 924350247, 906089663, 888235072, 870775310, 853699615, 836997608, 820659278, 804674961, 789035332, 773731380, 758754406, 744096000, 729748035, 715702649, 701952241, 688489454, 675307169, 662398491, 649756745, 637375462, 625248375, 613369408, 601732670, 590332448, 579163197, 568219537, 557496248, 546988257, 536690642, 526598616, 516707531, 507012869, 497510236, 488195360, 479064086, 470112371, 461336281, 452731986, 444295759, 436023970, 427913082, 419959651, 412160322, 404511823, 397010967, 389654646, 382439828, 375363557, 368422952, 361615197]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 392).prefactor = (4686499069635937/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 392).cutoff/(generalMeanRows 392).c)).2 =
    (10547553800369/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 392).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 392).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 392).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 392

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 392).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 392).criticalRate j.val*(generalMeanRows 392).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 392).c*(generalMeanRows 392).criticalPoint j.val)).2-
      (generalMeanRows 392).J/2-(generalMeanRows 392).error (generalMeanGrid j.val)+
      (generalMeanRows 392).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 392).c)).2-
      (generalMeanRows 392).J/2-(generalMeanRows 392).error 4 := by
  have he : (generalMeanRows 392).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 392) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 392)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0392

/-! Kernel-checked entropy margins for general spectral rectangle 393. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0393
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5155988776, 4986550048, 4824713272, 4670037941, 4522114969, 4380563943, 4245030678, 4115185022, 3990718889, 3871344484, 3756792702, 3646811682, 3541165494, 3439632943, 3342006482, 3248091223, 3157704030, 3070672689, 2986835143, 2906038802, 2828139891, 2753002865, 2680499859, 2610510187, 2542919873, 2477621223, 2414512425, 2353497177, 2294484343, 2237387638, 2182125326, 2128619946, 2076798056, 2026589991, 1977929638, 1930754231, 1885004154, 1840622758, 1797556192, 1755753241, 1715165181, 1675745633, 1637450439, 1600237533, 1564066828, 1528900108, 1494700926, 1461434509, 1429067667, 1397568707, 1366907360, 1337054698, 1307983070, 1279666031, 1252078285, 1225195621, 1198994858, 1173453797, 1148551169, 1124266585, 1100580498, 1077474160, 1054929577, 1032929482, 1011457290, 990497073, 970033522, 950051923, 930538126, 911478518, 892859999, 874669960, 856896256, 839527189, 822551485, 805958277, 789737085, 773877798, 758370662, 743206261, 728375499, 713869595, 699680062, 685798696, 672217567, 658929004, 645925587, 633200133, 620745691, 608555529, 596623126, 584942165, 573506524, 562310265, 551347633, 540613045, 530101085, 519806494, 509724169, 499849156, 490176642, 480701950, 471420538, 462327991, 453420014, 444692435, 436141192, 427762336, 419552025, 411506517, 403622172, 395895444, 388322881, 380901120, 373626886, 366496986, 359508310, 352657824, 345942573, 339359673, 332906314]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 393).prefactor = (4702350243428711/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 393).cutoff/(generalMeanRows 393).c)).2 =
    (25876755973991/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 393).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 393).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 393).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 393

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 393).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 393).criticalRate j.val*(generalMeanRows 393).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 393).c*(generalMeanRows 393).criticalPoint j.val)).2-
      (generalMeanRows 393).J/2-(generalMeanRows 393).error (generalMeanGrid j.val)+
      (generalMeanRows 393).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 393).c)).2-
      (generalMeanRows 393).J/2-(generalMeanRows 393).error 4 := by
  have he : (generalMeanRows 393).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 393) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 393)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0393

/-! Kernel-checked entropy margins for general spectral rectangle 394. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0394
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5087344240, 4917654364, 4755589641, 4600709731, 4452605623, 4310896904, 4175229318, 4045272577, 3920718400, 3801278749, 3686684230, 3576682653, 3471037720, 3369527839, 3271945042, 3178093991, 3087791084, 3000863619, 2917149044, 2836494256, 2758754962, 2683795089, 2611486241, 2541707197, 2474343443, 2409286750, 2346434768, 2285690663, 2226962769, 2170164275, 2115212925, 2062030744, 2010543782, 1960681873, 1912378413, 1865570152, 1820196997, 1776201834, 1733530355, 1692130897, 1651954298, 1612953753, 1575084684, 1538304618, 1502573071, 1467851440, 1434102901, 1401292312, 1369386128, 1338352310, 1308160250, 1278780695, 1250185675, 1222348440, 1195243394, 1168846037, 1143132912, 1118081546, 1093670410, 1069878864, 1046687116, 1024076181, 1002027841, 980524607, 959549685, 939086941, 919120873, 899636577, 880619720, 862056518, 843933701, 826238500, 808958615, 792082201, 775597842, 759494535, 743761669, 728389010, 713366684, 698685161, 684335239, 670308031, 656594952, 643187705, 630078270, 617258892, 604722069, 592460544, 580467293, 568735515, 557258625, 546030245, 535044195, 524294484, 513775307, 503481033, 493406200, 483545510, 473893822, 464446144, 455197631, 446143578, 437279413, 428600694, 420103107, 411782456, 403634663, 395655761, 387841892, 380189303, 372694344, 365353459, 358163189, 351120166, 344221109, 337462825, 330842202, 324356207, 318001885, 311776358, 305676818]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 394).prefactor = (2352116098497401/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 394).cutoff/(generalMeanRows 394).c)).2 =
    (100817511404327/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 394).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 394).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 394).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 394

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 394).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 394).criticalRate j.val*(generalMeanRows 394).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 394).c*(generalMeanRows 394).criticalPoint j.val)).2-
      (generalMeanRows 394).J/2-(generalMeanRows 394).error (generalMeanGrid j.val)+
      (generalMeanRows 394).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 394).c)).2-
      (generalMeanRows 394).J/2-(generalMeanRows 394).error 4 := by
  have he : (generalMeanRows 394).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 394) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 394)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0394

/-! Kernel-checked entropy margins for general spectral rectangle 395. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0395
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5104689964, 4934421516, 4771804220, 4616396234, 4467787153, 4325595267, 4189465110, 4059065271, 3934086416, 3814239526, 3699254288, 3588877651, 3482872512, 3381016525, 3283101011, 3188929968, 3098319165, 3011095314, 2927095307, 2846165520, 2768161167, 2692945712, 2620390321, 2550373359, 2482779924, 2417501414, 2354435133, 2293483916, 2234555784, 2177563631, 2122424919, 2069061410, 2017398898, 1967366981, 1918898826, 1871930969, 1826403111, 1782257943, 1739440971, 1697900358, 1657586774, 1618453253, 1580455066, 1543549596, 1507696219, 1472856202, 1438992594, 1406070135, 1374055164, 1342915534, 1312620531, 1283140804, 1254448287, 1226516139, 1199318676, 1172831315, 1147030518, 1121893739, 1097399371, 1073526705, 1050255883, 1027567854, 1005444339, 983867788, 962821349, 942288836, 922254692, 902703963, 883622267, 864995771, 846811163, 829055629, 811716827, 794782872, 778242308, 762084095, 746297586, 730872513, 715798968, 701067386, 686668537, 672593502, 658833667, 645380707, 632226574, 619363487, 606783920, 594480588, 582446445, 570674666, 559158645, 547891981, 536868473, 526082110, 515527067, 505197693, 495088509, 485194199, 475509602, 466029712, 456749666, 447664742, 438770353, 430062044, 421535484, 413186463, 405010889, 397004782, 389164271, 381485590, 373965076, 366599162, 359384376, 352317339, 345394760, 338613433, 331970236, 325462126, 319086139, 312839385, 306719048]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 395).prefactor = (1180067917191777/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 395).cutoff/(generalMeanRows 395).c)).2 =
    (100817511404327/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 395).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 395).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 395).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 395

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 395).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 395).criticalRate j.val*(generalMeanRows 395).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 395).c*(generalMeanRows 395).criticalPoint j.val)).2-
      (generalMeanRows 395).J/2-(generalMeanRows 395).error (generalMeanGrid j.val)+
      (generalMeanRows 395).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 395).c)).2-
      (generalMeanRows 395).J/2-(generalMeanRows 395).error 4 := by
  have he : (generalMeanRows 395).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 395) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 395)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0395

/-! Kernel-checked entropy margins for general spectral rectangle 396. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0396
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5153802224, 4984431059, 4822673021, 4668085892, 4520259039, 4378810662, 4243385324, 4113651753, 3989300859, 3870043947, 3755611112, 3645749782, 3540223392, 3438810188, 3341302132, 3247503905, 3157231992, 3070313851, 2986587147, 2905899046, 2828105572, 2753071009, 2680667353, 2610773806, 2543276305, 2478067091, 2415044305, 2354111618, 2295177883, 2238156818, 2182966702, 2129530100, 2077773605, 2027627596, 1979026013, 1931906149, 1886208451, 1841876338, 1798856031, 1757096393, 1716548776, 1677166883, 1638906638, 1601726057, 1565585138, 1530445750, 1496271530, 1463027787, 1430681417, 1399200811, 1368555779, 1338717477, 1309658331, 1281351977, 1253773193, 1226897845, 1200702827, 1175166009, 1150266193, 1125983060, 1102297128, 1079189713, 1056642885, 1034639437, 1013162843, 992197231, 971727350, 951738536, 932216691, 913148252, 894520168, 876319874, 858535269, 841154700, 824166931, 807561136, 791326872, 775454064, 759932994, 744754276, 729908849, 715387960, 701183151, 687286247, 673689344, 660384796, 647365206, 634623415, 622152493, 609945729, 597996622, 586298873, 574846377, 563633214, 552653644, 541902100, 531373179, 521061635, 510962380, 501070470, 491381103, 481889613, 472591469, 463482263, 454557711, 445813647, 437246019, 428850884, 420624405, 412562848, 404662578, 396920054, 389331830, 381894547, 374604933, 367459800, 360456040, 353590623, 346860597, 340263081, 333795266]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 396).prefactor = (471622362165803/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 396).cutoff/(generalMeanRows 396).c)).2 =
    (52122788435161/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 396).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 396).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 396).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 396

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 396).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 396).criticalRate j.val*(generalMeanRows 396).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 396).c*(generalMeanRows 396).criticalPoint j.val)).2-
      (generalMeanRows 396).J/2-(generalMeanRows 396).error (generalMeanGrid j.val)+
      (generalMeanRows 396).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 396).c)).2-
      (generalMeanRows 396).J/2-(generalMeanRows 396).error 4 := by
  have he : (generalMeanRows 396).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 396) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 396)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0396

/-! Kernel-checked entropy margins for general spectral rectangle 397. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0397
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5279285943, 5108434758, 4945238120, 4789250883, 4640059727, 4497280380, 4360555136, 4229550630, 4103955847, 3983480321, 3867852514, 3756818347, 3650139871, 3547594052, 3448971675, 3354076333, 3262723511, 3174739746, 3089961852, 3008236211, 2929418128, 2853371223, 2779966881, 2709083742, 2640607228, 2574429105, 2510447078, 2448564421, 2388689618, 2330736053, 2274621696, 2220268833, 2167603800, 2116556742, 2067061387, 2019054831, 1972477347, 1927272192, 1883385445, 1840765834, 1799364594, 1759135323, 1720033845, 1682018094, 1645047989, 1609085329, 1574093691, 1540038331, 1506886094, 1474605331, 1443165813, 1412538665, 1382696285, 1353612283, 1325261417, 1297619535, 1270663516, 1244371217, 1218721429, 1193693824, 1169268914, 1145428008, 1122153172, 1099427194, 1077233547, 1055556355, 1034380366, 1013690915, 993473902, 973715763, 954403445, 935524383, 917066475, 899018064, 881367915, 864105197, 847219465, 830700642, 814539003, 798725160, 783250046, 768104902, 753281264, 738770950, 724566047, 710658901, 697042106, 683708493, 670651120, 657863265, 645338415, 633070257, 621052672, 609279726, 597745665, 586444902, 575372020, 564521755, 553889000, 543468792, 533256309, 523246867, 513435910, 503819011, 494391863, 485150277, 476090177, 467207596, 458498674, 449959649, 441586862, 433376746, 425325827, 417430719, 409688123, 402094822, 394647680, 387343638, 380179715, 373152998, 366260650]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 397).prefactor = (4747926258742349/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 397).cutoff/(generalMeanRows 397).c)).2 =
    (424856363912193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 397).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 397).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 397).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 397

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 397).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 397).criticalRate j.val*(generalMeanRows 397).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 397).c*(generalMeanRows 397).criticalPoint j.val)).2-
      (generalMeanRows 397).J/2-(generalMeanRows 397).error (generalMeanGrid j.val)+
      (generalMeanRows 397).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 397).c)).2-
      (generalMeanRows 397).J/2-(generalMeanRows 397).error 4 := by
  have he : (generalMeanRows 397).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 397) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 397)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0397

/-! Kernel-checked entropy margins for general spectral rectangle 398. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0398
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5173427907, 5003416086, 4841031929, 4685833439, 4537410145, 4395380351, 4259388671, 4129103837, 4004216722, 3884438556, 3769499324, 3659146315, 3553142800, 3451266834, 3353310170, 3259077261, 3168384352, 3081058643, 2996937533, 2915867914, 2837705525, 2762314363, 2689566129, 2619339731, 2551520806, 2486001297, 2422679045, 2361457424, 2302244991, 2244955167, 2189505941, 2135819590, 2083822423, 2033444538, 1984619601, 1937284632, 1891379815, 1846848308, 1803636077, 1761691736, 1720966394, 1681413518, 1642988798, 1605650026, 1569356980, 1534071316, 1499756462, 1466377528, 1433901211, 1402295712, 1371530659, 1341577026, 1312407069, 1283994253, 1256313197, 1229339607, 1203050225, 1177422777, 1152435920, 1128069199, 1104302998, 1081118507, 1058497672, 1036423165, 1014878348, 993847237, 973314472, 953265290, 933685491, 914561417, 895879925, 877628361, 859794541, 842366727, 825333606, 808684274, 792408217, 776495290, 760935704, 745720012, 730839088, 716284121, 702046594, 688118277, 674491212, 661157704, 648110304, 635341809, 622845243, 610613850, 598641088, 586920619, 575446298, 564212170, 553212459, 542441564, 531894049, 521564638, 511448212, 501539799, 491834569, 482327831, 473015027, 463891725, 454953619, 446196520, 437616355, 429209160, 420971078, 412898358, 404987345, 397234483, 389636308, 382189444, 374890607, 367736591, 360724277, 353850621, 347112656, 340507491, 334032305]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 398).prefactor = (4718255030741271/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 398).cutoff/(generalMeanRows 398).c)).2 =
    (25876755973991/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 398).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 398).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 398).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 398

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 398).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 398).criticalRate j.val*(generalMeanRows 398).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 398).c*(generalMeanRows 398).criticalPoint j.val)).2-
      (generalMeanRows 398).J/2-(generalMeanRows 398).error (generalMeanGrid j.val)+
      (generalMeanRows 398).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 398).c)).2-
      (generalMeanRows 398).J/2-(generalMeanRows 398).error 4 := by
  have he : (generalMeanRows 398).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 398) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 398)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0398

/-! Kernel-checked entropy margins for general spectral rectangle 399. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0399
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5190926023, 5020339170, 4857405780, 4701682361, 4552757055, 4410246872, 4273795226, 4143069730, 4017760208, 3897576915, 3782248924, 3671522668, 3565160616, 3462940074, 3364652091, 3270100458, 3179100797, 3091479726, 3007074093, 2925730271, 2847303513, 2771657355, 2698663065, 2628199139, 2560150830, 2494409714, 2430873287, 2369444596, 2310031888, 2252548292, 2196911520, 2143043585, 2090870548, 2040322270, 1991332192, 1943837122, 1897777040, 1853094914, 1809736526, 1767650316, 1726787229, 1687100573, 1648545888, 1611080825, 1574665026, 1539260015, 1504829097, 1471337265, 1438751103, 1407038705, 1376169595, 1346114650, 1316846031, 1288337115, 1260562433, 1233497610, 1207119309, 1181405181, 1156333811, 1131884674, 1108038089, 1084775181, 1062077835, 1039928666, 1018310977, 997208732, 976606520, 956489524, 936843501, 917654744, 898910065, 880596769, 862702630, 845215869, 828125137, 811419492, 795088384, 779121634, 763509421, 748242265, 733311009, 718706813, 704421130, 690445704, 676772548, 663393941, 650302412, 637490730, 624951896, 612679133, 600665875, 588905764, 577392634, 566120508, 555083593, 544276267, 533693077, 523328729, 513178087, 503236160, 493498104, 483959211, 474614908, 465460749, 456492412, 447705694, 439096507, 430660876, 422394931, 414294907, 406357136, 398578052, 390954177, 383482126, 376158601, 368980389, 361944357, 355047452, 348286697, 341659192, 335162105]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 399).prefactor = (4734213612910951/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 399).cutoff/(generalMeanRows 399).c)).2 =
    (25876755973991/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 399).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 399).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 399).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 399

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 399).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 399).criticalRate j.val*(generalMeanRows 399).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 399).c*(generalMeanRows 399).criticalPoint j.val)).2-
      (generalMeanRows 399).J/2-(generalMeanRows 399).error (generalMeanGrid j.val)+
      (generalMeanRows 399).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 399).c)).2-
      (generalMeanRows 399).J/2-(generalMeanRows 399).error 4 := by
  have he : (generalMeanRows 399).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 399) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 399)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0399

/-! Kernel-checked entropy margins for general spectral rectangle 400. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0400
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5035310267, 4864880892, 4702137550, 4546636779, 4397966642, 4255743975, 4119611932, 3989237785, 3864310952, 3744541220, 3629657138, 3519404567, 3413545364, 3311856185, 3214127397, 3120162082, 3029775132, 2942792416, 2859050014, 2778393524, 2700677411, 2625764419, 2553525019, 2483836908, 2416584541, 2351658698, 2288956083, 2228378955, 2169834781, 2113235918, 2058499314, 2005546228, 1954301979, 1904695696, 1856660101, 1810131296, 1765048568, 1721354204, 1678993323, 1637913713, 1598065681, 1559401914, 1521877347, 1485449037, 1450076048, 1415719344, 1382341685, 1349907528, 1318382942, 1287735519, 1257934296, 1228949676, 1200753363, 1173318289, 1146618555, 1120629370, 1095326995, 1070688690, 1046692666, 1023318034, 1000544764, 978353642, 956726229, 935644825, 915092434, 895052728, 875510017, 856449218, 837855829, 819715898, 802016001, 784743214, 767885097, 751429664, 735365367, 719681077, 704366061, 689409972, 674802823, 660534980, 646597140, 632980321, 619675846, 606675331, 593970675, 581554043, 569417859, 557554794, 545957759, 534619887, 523534536, 512695269, 502095852, 491730245, 481592595, 471677226, 461978635, 452491484, 443210595, 434130944, 425247653, 416555986, 408051346, 399729267, 391585410, 383615559, 375815616, 368181599, 360709633, 353395954, 346236896, 339228897, 332368487, 325652291, 319077024, 312639486, 306336562, 300165220, 294122503, 288205532, 282411503]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 400).prefactor = (1184091457113829/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 400).cutoff/(generalMeanRows 400).c)).2 =
    (395518068812987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 400).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 400).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 400).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 400

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 400).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 400).criticalRate j.val*(generalMeanRows 400).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 400).c*(generalMeanRows 400).criticalPoint j.val)).2-
      (generalMeanRows 400).J/2-(generalMeanRows 400).error (generalMeanGrid j.val)+
      (generalMeanRows 400).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 400).c)).2-
      (generalMeanRows 400).J/2-(generalMeanRows 400).error 4 := by
  have he : (generalMeanRows 400).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 400) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 400)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0400

/-! Kernel-checked entropy margins for general spectral rectangle 401. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0401
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5052478577, 4881468108, 4718169879, 4562138916, 4412961876, 4270254289, 4133658092, 4002839423, 3877486643, 3757308546, 3642032757, 3531404271, 3425184132, 3323148235, 3225086232, 3130800535, 3040105403, 2952826112, 2868798183, 2787866688, 2709885596, 2634717181, 2562231475, 2492305757, 2424824088, 2359676874, 2296760470, 2235976799, 2177233014, 2120441172, 2065517939, 2012384305, 1960965334, 1911189914, 1862990538, 1816303090, 1771066648, 1727223305, 1684717991, 1643498316, 1603514419, 1564718825, 1527066315, 1490513799, 1455020203, 1420546357, 1387054894, 1354510150, 1322878079, 1292126161, 1262223328, 1233139883, 1204847432, 1177318816, 1150528047, 1124450249, 1099061604, 1074339293, 1050261452, 1026807122, 1003956205, 981689420, 959988267, 938834984, 918212518, 898104485, 878495141, 859369353, 840712568, 822510788, 804750541, 787418862, 770503266, 753991726, 737872657, 722134889, 706767656, 691760573, 677103620, 662787129, 648801767, 635138520, 621788682, 608743841, 595995867, 583536900, 571359336, 559455824, 547819247, 536442718, 525319570, 514443346, 503807789, 493406840, 483234625, 473285449, 463553789, 454034291, 444721759, 435611150, 426697570, 417976268, 409442631, 401092177, 392920553, 384923528, 377096991, 369436944, 361939503, 354600887, 347417420, 340385526, 333501725, 326762630, 320164943, 313705456, 307381042, 301188658, 295125338, 289188193, 283374409]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 401).prefactor = (4752514862522413/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 401).cutoff/(generalMeanRows 401).c)).2 =
    (395518068812987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 401).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 401).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 401).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 401

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 401).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 401).criticalRate j.val*(generalMeanRows 401).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 401).c*(generalMeanRows 401).criticalPoint j.val)).2-
      (generalMeanRows 401).J/2-(generalMeanRows 401).error (generalMeanGrid j.val)+
      (generalMeanRows 401).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 401).c)).2-
      (generalMeanRows 401).J/2-(generalMeanRows 401).error 4 := by
  have he : (generalMeanRows 401).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 401) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 401)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0401

/-! Kernel-checked entropy margins for general spectral rectangle 402. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0402
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5001257347, 4829537583, 4665591124, 4508969816, 4359257332, 4216066399, 4079036315, 3947830735, 3822135673, 3701657709, 3586122374, 3475272680, 3368867793, 3266681826, 3168502739, 3074131337, 2983380351, 2896073601, 2812045226, 2731138976, 2653207562, 2578112058, 2505721349, 2435911620, 2368565887, 2303573556, 2240830024, 2180236302, 2121698666, 2065128336, 2010441172, 1957557398, 1906401339, 1856901178, 1808988730, 1762599229, 1717671132, 1674145932, 1631967986, 1591084356, 1551444650, 1513000888, 1475707365, 1439520523, 1404398840, 1370302717, 1337194371, 1305037745, 1273798410, 1243443481, 1213941539, 1185262550, 1157377798, 1130259813, 1103882308, 1078220124, 1053249166, 1028946354, 1005289571, 982257617, 959830160, 937987699, 916711520, 895983658, 875786862, 856104562, 836920836, 818220379, 799988472, 782210961, 764874225, 747965156, 731471130, 715379991, 699680028, 684359954, 669408887, 654816336, 640572177, 626666646, 613090314, 599834082, 586889158, 574247051, 561899556, 549838741, 538056936, 526546724, 515300931, 504312612, 493575047, 483081728, 472826354, 462802820, 453005211, 443427794, 434065014, 424911480, 415961968, 407211407, 398654878, 390287606, 382104957, 374102430, 366275655, 358620387, 351132501, 343807989, 336642954, 329633610, 322776274, 316067365, 309503399, 303080987, 296796831, 290647723, 284630538, 278742236, 272979855, 267340512, 261821397]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 402).prefactor = (4784978302826323/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 402).cutoff/(generalMeanRows 402).c)).2 =
    (38782572318983/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 402).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 402).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 402).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 402

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 402).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 402).criticalRate j.val*(generalMeanRows 402).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 402).c*(generalMeanRows 402).criticalPoint j.val)).2-
      (generalMeanRows 402).J/2-(generalMeanRows 402).error (generalMeanGrid j.val)+
      (generalMeanRows 402).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 402).c)).2-
      (generalMeanRows 402).J/2-(generalMeanRows 402).error 4 := by
  have he : (generalMeanRows 402).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 402) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 402)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0402

/-! Kernel-checked entropy margins for general spectral rectangle 403. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0403
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5177293925, 5007178457, 4844666541, 4689319688, 4540730592, 4398520406, 4262336318, 4131849370, 4006752510, 3886758830, 3771599978, 3661024728, 3554797673, 3452698044, 3354518631, 3260064801, 3169153603, 3081612940, 2997280817, 2916004651, 2837640630, 2762053129, 2689114168, 2618702911, 2550705209, 2485013164, 2421524742, 2360143399, 2300777745, 2243341223, 2187751816, 2133931775, 2081807358, 2031308598, 1982369076, 1934925717, 1888918592, 1844290743, 1800988006, 1758958859, 1718154268, 1678527554, 1640034255, 1602632009, 1566280437, 1530941037, 1496577078, 1463153512, 1430636876, 1398995214, 1368197998, 1338216046, 1309021462, 1280587562, 1252888814, 1225900780, 1199600061, 1173964242, 1148971846, 1124602283, 1100835811, 1077653490, 1055037148, 1032969336, 1011433302, 990412949, 969892811, 949858019, 930294274, 911187819, 892525417, 874294324, 856482269, 839077429, 822068411, 805444234, 789194308, 773308417, 757776705, 742589656, 727738085, 713213117, 699006180, 685108988, 671513530, 658212061, 645197085, 632461352, 619997843, 607799762, 595860526, 584173761, 572733285, 561533111, 550567430, 539830610, 529317188, 519021861, 508939484, 499065061, 489393739, 479920806, 470641683, 461551921, 452647196, 443923301, 435376147, 427001758, 418796263, 410755897, 402876995, 395155989, 387589404, 380173859, 372906057, 365782787, 358800921, 351957411, 345249283, 338673640, 332227657]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 403).prefactor = (4689977528016961/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 403).cutoff/(generalMeanRows 403).c)).2 =
    (102036431420197/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 403).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 403).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 403).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 403

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 403).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 403).criticalRate j.val*(generalMeanRows 403).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 403).c*(generalMeanRows 403).criticalPoint j.val)).2-
      (generalMeanRows 403).J/2-(generalMeanRows 403).error (generalMeanGrid j.val)+
      (generalMeanRows 403).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 403).c)).2-
      (generalMeanRows 403).J/2-(generalMeanRows 403).error 4 := by
  have he : (generalMeanRows 403).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 403) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 403)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0403

/-! Kernel-checked entropy margins for general spectral rectangle 404. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0404
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5106825701, 4936508489, 4773830148, 4618350592, 4469661005, 4327381110, 4191156731, 4060657618, 3935575483, 3815622242, 3700528421, 3590041718, 3483925699, 3381958609, 3283932295, 3189651220, 3098931561, 3011600386, 2927494898, 2846461739, 2768356356, 2693042406, 2620391219, 2550281295, 2482597843, 2417232348, 2354082179, 2293050216, 2234044514, 2176977980, 2121768079, 2068336561, 2016609203, 1966515570, 1917988793, 1870965361, 1825384926, 1781190121, 1738326392, 1696741835, 1656387052, 1617215007, 1579180899, 1542242033, 1506357712, 1471489124, 1437599243, 1404652730, 1372615846, 1341456369, 1311143507, 1281647833, 1252941208, 1224996715, 1197788599, 1171292205, 1145483926, 1120341145, 1095842191, 1071966290, 1048693518, 1026004764, 1003881687, 982306680, 961262835, 940733909, 920704292, 901158979, 882083539, 863464090, 845287273, 827540229, 810210575, 793286382, 776756156, 760608817, 744833683, 729420448, 714359171, 699640255, 685254438, 671192772, 657446614, 644007611, 630867690, 618019044, 605454123, 593165621, 581146469, 569389822, 557889054, 546637745, 535629677, 524858823, 514319340, 504005564, 493912000, 484033319, 474364349, 464900070, 455635607, 446566229, 437687340, 428994473, 420483288, 412149569, 403989214, 395998237, 388172760, 380509011, 373003320, 365652115, 358451920, 351399350, 344491110, 337723991, 331094866, 324600689, 318238494, 312005388, 305898552]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 404).prefactor = (2353049031288557/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 404).cutoff/(generalMeanRows 404).c)).2 =
    (100083296485999/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 404).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 404).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 404).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 404

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 404).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 404).criticalRate j.val*(generalMeanRows 404).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 404).c*(generalMeanRows 404).criticalPoint j.val)).2-
      (generalMeanRows 404).J/2-(generalMeanRows 404).error (generalMeanGrid j.val)+
      (generalMeanRows 404).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 404).c)).2-
      (generalMeanRows 404).J/2-(generalMeanRows 404).error 4 := by
  have he : (generalMeanRows 404).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 404) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 404)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0404

/-! Kernel-checked entropy margins for general spectral rectangle 405. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0405
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5039975839, 4869454863, 4706594909, 4550956042, 4402129508, 4259735021, 4123418329, 3992849039, 3867718670, 3747738895, 3632639952, 3522169214, 3416089885, 3314179821, 3216230453, 3122045804, 3031441593, 2944244414, 2860290981, 2779427440, 2701508726, 2626397985, 2553966026, 2484090829, 2416657078, 2351555735, 2288683646, 2227943175, 2169241857, 2112492088, 2057610829, 2004519328, 1953142869, 1903410531, 1855254967, 1808612195, 1763421406, 1719624780, 1677167320, 1635996689, 1596063065, 1557318997, 1519719278, 1483220821, 1447782544, 1413365261, 1379931581, 1347445811, 1315873869, 1285183196, 1255342679, 1226322575, 1198094438, 1170631058, 1143906392, 1117895511, 1092574537, 1067920596, 1043911768, 1020527035, 997746242, 975550054, 953919912, 932838001, 912287213, 892251111, 872713901, 853660397, 835075999, 816946660, 799258863, 781999598, 765156336, 748717011, 732669996, 717004084, 701708471, 686772737, 672186830, 657941050, 644026033, 630432736, 617152426, 604176666, 591497301, 579106447, 566996481, 555160029, 543589956, 532279359, 521221553, 510410065, 499838627, 489501165, 479391792, 469504804, 459834669, 450376022, 441123660, 432072533, 423217742, 414554529, 406078277, 397784500, 389668842, 381727070, 373955071, 366348846, 358904510, 351618282, 344486488, 337505552, 330671995, 323982432, 317433569, 311022200, 304745200, 298599531, 292582230, 286690413, 280921270]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 405).prefactor = (94158965879761/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 405).cutoff/(generalMeanRows 405).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 405).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 405).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 405).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 405

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 405).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 405).criticalRate j.val*(generalMeanRows 405).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 405).c*(generalMeanRows 405).criticalPoint j.val)).2-
      (generalMeanRows 405).J/2-(generalMeanRows 405).error (generalMeanGrid j.val)+
      (generalMeanRows 405).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 405).c)).2-
      (generalMeanRows 405).J/2-(generalMeanRows 405).error 4 := by
  have he : (generalMeanRows 405).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 405) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 405)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0405

/-! Kernel-checked entropy margins for general spectral rectangle 406. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0406
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5057440649, 4886328774, 4722904469, 4566726273, 4417384017, 4274496097, 4137707032, 4006685286, 3881121309, 3760725773, 3645227982, 3534374434, 3427927513, 3325664305, 3227375517, 3132864494, 3041946317, 2954446977, 2870202624, 2789058869, 2710870147, 2635499128, 2562816174, 2492698842, 2425031415, 2359704479, 2296614523, 2235663570, 2176758837, 2119812416, 2064740979, 2011465502, 1959911011, 1910006337, 1861683902, 1814879500, 1769532113, 1725583721, 1682979135, 1641665838, 1601593833, 1562715507, 1524985495, 1488360562, 1452799483, 1418262935, 1384713398, 1352115057, 1320433710, 1289636686, 1259692764, 1230572097, 1202246143, 1174687595, 1147870322, 1121769306, 1096360588, 1071621215, 1047529190, 1024063423, 1001203689, 978930585, 957225489, 936070524, 915448522, 895342990, 875738079, 856618550, 837969752, 819777590, 802028500, 784709427, 767807799, 751311508, 735208885, 719488687, 704140071, 689152581, 674516130, 660220985, 646257748, 632617347, 619291018, 606270294, 593546991, 581113199, 568961269, 557083801, 545473635, 534123844, 523027720, 512178767, 501570696, 491197412, 481053008, 471131759, 461428114, 451936691, 442652267, 433569775, 424684300, 415991067, 407485442, 399162925, 391019144, 383049852, 375250921, 367618339, 360148206, 352836730, 345680222, 338675095, 331817858, 325105114, 318533558, 312099971, 305801221, 299634255, 293596103, 287683869, 281894734]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 406).prefactor = (36908301122203/7812500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 406).cutoff/(generalMeanRows 406).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 406).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 406).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 406).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 406

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 406).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 406).criticalRate j.val*(generalMeanRows 406).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 406).c*(generalMeanRows 406).criticalPoint j.val)).2-
      (generalMeanRows 406).J/2-(generalMeanRows 406).error (generalMeanGrid j.val)+
      (generalMeanRows 406).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 406).c)).2-
      (generalMeanRows 406).J/2-(generalMeanRows 406).error 4 := by
  have he : (generalMeanRows 406).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 406) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 406)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0406

/-! Kernel-checked entropy margins for general spectral rectangle 407. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0407
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5037776228, 4867294116, 4704485881, 4548909810, 4400155543, 4257841340, 4121611639, 3991134867, 3866101481, 3746222196, 3631226396, 3520860685, 3414887584, 3313084337, 3215241834, 3121163618, 3030664984, 2943572155, 2859721519, 2778958940, 2701139111, 2626124967, 2553787144, 2484003471, 2416658511, 2351643129, 2288854094, 2228193712, 2169569479, 2112893765, 2058083519, 2005059992, 1953748478, 1904078079, 1855981477, 1809394730, 1764257071, 1720510732, 1678100768, 1636974904, 1597083378, 1558378806, 1520816049, 1484352089, 1448945915, 1414558414, 1381152268, 1348691857, 1317143172, 1286473729, 1256652488, 1227649776, 1199437222, 1171987685, 1145275193, 1119274885, 1093962950, 1069316582, 1045313923, 1021934020, 999156780, 976962926, 955333960, 934252123, 913700362, 893662295, 874122178, 855064877, 836475839, 818341065, 800647085, 783380930, 766530117, 750082617, 734026844, 718351629, 703046204, 688100185, 673503552, 659246637, 645320107, 631714950, 618422461, 605434228, 592742122, 580338286, 568215119, 556365271, 544781627, 533457304, 522385637, 511560173, 500974659, 490623038, 480499442, 470598179, 460913732, 451440749, 442174041, 433108569, 424239446, 415561925, 407071397, 398763389, 390633551, 382677659, 374891609, 367271409, 359813179, 352513147, 345367643, 338373098, 331526037, 324823082, 318260940, 311836411, 305546374, 299387794, 293357710, 287453243, 281671584]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 407).prefactor = (236113700356647/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 407).cutoff/(generalMeanRows 407).c)).2 =
    (392581209139677/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 407).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 407).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 407).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 407

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 407).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 407).criticalRate j.val*(generalMeanRows 407).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 407).c*(generalMeanRows 407).criticalPoint j.val)).2-
      (generalMeanRows 407).J/2-(generalMeanRows 407).error (generalMeanGrid j.val)+
      (generalMeanRows 407).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 407).c)).2-
      (generalMeanRows 407).J/2-(generalMeanRows 407).error 4 := by
  have he : (generalMeanRows 407).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 407) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 407)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0407

/-! Kernel-checked entropy margins for general spectral rectangle 408. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0408
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4970115106, 4799503534, 4636600502, 4480962635, 4332177999, 4189863366, 4053661757, 3923240255, 3798288036, 3678514597, 3563648158, 3453434213, 3347634221, 3246024413, 3148394705, 3054547711, 2964297833, 2877470437, 2793901093, 2713434874, 2635925715, 2561235825, 2489235138, 2419800811, 2352816760, 2288173225, 2225766377, 2165497943, 2107274862, 2051008970, 1996616700, 1944018805, 1893140100, 1843909226, 1796258421, 1750123312, 1705442722, 1662158483, 1620215270, 1579560435, 1540143861, 1501917823, 1464836850, 1428857607, 1393938778, 1360040952, 1327126530, 1295159617, 1264105943, 1233932770, 1204608814, 1176104169, 1148390239, 1121439667, 1095226273, 1069724995, 1044911834, 1020763797, 997258851, 974375874, 952094609, 930395626, 909260277, 888670660, 868609586, 849060542, 830007660, 811435687, 793329957, 775676361, 758461326, 741671786, 725295162, 709319338, 693732642, 678523825, 663682044, 649196841, 635058129, 621256176, 607781587, 594625294, 581778536, 569232854, 556980070, 545012281, 533321848, 521901380, 510743728, 499841976, 489189429, 478779605, 468606227, 458663216, 448944680, 439444911, 430158375, 421079706, 412203702, 403525314, 395039644, 386741941, 378627591, 370692113, 362931159, 355340504, 347916042, 340653785, 333549857, 326600490, 319802020, 313150885, 306643619, 300276851, 294047302, 287951781, 281987180, 276150475, 270438724, 264849058, 259378685]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 408).prefactor = (4738505552141363/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 408).cutoff/(generalMeanRows 408).c)).2 =
    (96222215879131/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 408).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 408).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 408).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 408

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 408).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 408).criticalRate j.val*(generalMeanRows 408).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 408).c*(generalMeanRows 408).criticalPoint j.val)).2-
      (generalMeanRows 408).J/2-(generalMeanRows 408).error (generalMeanGrid j.val)+
      (generalMeanRows 408).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 408).c)).2-
      (generalMeanRows 408).J/2-(generalMeanRows 408).error 4 := by
  have he : (generalMeanRows 408).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 408) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 408)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0408

/-! Kernel-checked entropy margins for general spectral rectangle 409. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0409
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4989874066, 4818628109, 4655104635, 4498860504, 4349483963, 4206591901, 4069827410, 3938857599, 3813371625, 3693078933, 3577707654, 3467003165, 3360726782, 3258654568, 3160576250, 3066294237, 2975622710, 2888386801, 2804421831, 2723572618, 2645692834, 2570644416, 2498297023, 2428527534, 2361219580, 2296263122, 2233554044, 2172993788, 2114489013, 2057951273, 2003296719, 1950445830, 1899323148, 1849857043, 1801979488, 1755625849, 1710734690, 1667247594, 1625108987, 1584265979, 1544668218, 1506267746, 1469018867, 1432878025, 1397803690, 1363756242, 1330697876, 1298592502, 1267405656, 1237104412, 1207657305, 1179034254, 1151206489, 1124146489, 1097827913, 1072225544, 1047315229, 1023073832, 999479179, 976510009, 954145935, 932367398, 911155627, 890492601, 870361017, 850744249, 831626324, 812991884, 794826164, 777114958, 759844602, 743001939, 726574305, 710549501, 694915775, 679661801, 664776662, 650249828, 636071146, 622230814, 608719378, 595527705, 582646978, 570068680, 557784579, 545786721, 534067415, 522619222, 511434949, 500507633, 489830537, 479397138, 469201120, 459236365, 449496945, 439977118, 430671316, 421574141, 412680358, 403984891, 395482814, 387169346, 379039847, 371089814, 363314872, 355710773, 348273390, 340998713, 333882847, 326922002, 320112497, 313450751, 306933281, 300556700, 294317713, 288213112, 282239777, 276394669, 270674832, 265077385, 259599523]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 409).prefactor = (296289582897489/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 409).cutoff/(generalMeanRows 409).c)).2 =
    (76392120747487/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 409).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 409).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 409).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 409

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 409).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 409).criticalRate j.val*(generalMeanRows 409).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 409).c*(generalMeanRows 409).criticalPoint j.val)).2-
      (generalMeanRows 409).J/2-(generalMeanRows 409).error (generalMeanGrid j.val)+
      (generalMeanRows 409).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 409).c)).2-
      (generalMeanRows 409).J/2-(generalMeanRows 409).error 4 := by
  have he : (generalMeanRows 409).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 409) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 409)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0409

/-! Kernel-checked entropy margins for general spectral rectangle 410. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0410
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4923663302, 4752317344, 4588728409, 4432451649, 4283073692, 4140209898, 4003501906, 3872615444, 3747238359, 3627078846, 3511863845, 3401337599, 3295260338, 3193407090, 3095566592, 3001540303, 2911141498, 2824194437, 2740533609, 2660003031, 2582455608, 2507752540, 2435762778, 2366362522, 2299434751, 2234868795, 2172559938, 2112409040, 2054322202, 1998210441, 1943989394, 1891579041, 1840903446, 1791890521, 1744471795, 1698582209, 1654159919, 1611146111, 1569484834, 1529122833, 1490009406, 1452096256, 1415337363, 1379688861, 1345108918, 1311557627, 1278996906, 1247390399, 1216703386, 1186902696, 1157956628, 1129834874, 1102508450, 1075949625, 1050131859, 1025029742, 1000618942, 976876144, 953779007, 931306110, 909436913, 888151710, 867431588, 847258396, 827614699, 808483752, 789849465, 771696371, 754009599, 736774844, 719978345, 703606859, 687647634, 672088391, 656917302, 642122970, 627694408, 613621026, 599892606, 586499295, 573431582, 560680286, 548236546, 536091800, 524237778, 512666489, 501370207, 490341465, 479573039, 469057941, 458789412, 448760908, 438966094, 429398837, 420053195, 410923412, 402003912, 393289289, 384774302, 376453870, 368323064, 360377104, 352611349, 345021297, 337602579, 330350951, 323262292, 316332601, 309557988, 302934677, 296458996, 290127377, 283936349, 277882541, 271962671, 266173548, 260512069, 254975212, 249560040, 244263690, 239083379]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 410).prefactor = (951412167608631/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 410).cutoff/(generalMeanRows 410).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 410).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 410).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 410).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 410

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 410).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 410).criticalRate j.val*(generalMeanRows 410).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 410).c*(generalMeanRows 410).criticalPoint j.val)).2-
      (generalMeanRows 410).J/2-(generalMeanRows 410).error (generalMeanGrid j.val)+
      (generalMeanRows 410).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 410).c)).2-
      (generalMeanRows 410).J/2-(generalMeanRows 410).error 4 := by
  have he : (generalMeanRows 410).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 410) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 410)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0410

/-! Kernel-checked entropy margins for general spectral rectangle 411. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0411
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4992283244, 4821003311, 4657432605, 4501129780, 4351684703, 4208715728, 4071867273, 3940807641, 3815227066, 3694835960, 3579363325, 3468555320, 3362173956, 3259995919, 3161811494, 3067423579, 2976646791, 2889306645, 2805238798, 2724288361, 2646309261, 2571163652, 2498721380, 2428859481, 2361461717, 2296418154, 2233624761, 2172983048, 2114399720, 2057786362, 2003059147, 1950138556, 1898949126, 1849419213, 1801480763, 1755069111, 1710122784, 1666583316, 1624395085, 1583505147, 1543863091, 1505420897, 1468132805, 1431955194, 1396846464, 1362766928, 1329678710, 1297545649, 1266333210, 1236008396, 1206539672, 1177896886, 1150051199, 1122975020, 1096641940, 1071026674, 1046105007, 1021853734, 998250618, 975274338, 952904445, 931121322, 909906139, 889240820, 869108007, 849491021, 830373838, 811741049, 793577843, 775869966, 758603708, 741765871, 725343747, 709325096, 693698129, 678451482, 663574200, 649055720, 634885854, 621054771, 607552983, 594371328, 581500963, 568933341, 556660207, 544673580, 532965746, 521529244, 510356858, 499441606, 488776731, 478355691, 468172152, 458219979, 448493230, 438986146, 429693144, 420608814, 411727908, 403045336, 394556161, 386255592, 378138978, 370201807, 362439693, 354848382, 347423737, 340161742, 333058493, 326110195, 319313159, 312663800, 306158629, 299794254, 293567374, 287474780, 281513345, 275680028, 269971869, 264385984, 258919566]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 411).prefactor = (4726237803964871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 411).cutoff/(generalMeanRows 411).c)).2 =
    (189520446817049/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 411).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 411).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 411).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 411

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 411).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 411).criticalRate j.val*(generalMeanRows 411).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 411).c*(generalMeanRows 411).criticalPoint j.val)).2-
      (generalMeanRows 411).J/2-(generalMeanRows 411).error (generalMeanGrid j.val)+
      (generalMeanRows 411).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 411).c)).2-
      (generalMeanRows 411).J/2-(generalMeanRows 411).error 4 := by
  have he : (generalMeanRows 411).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 411) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 411)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0411

/-! Kernel-checked entropy margins for general spectral rectangle 412. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0412
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4926397332, 4755013037, 4591372645, 4435033090, 4285582612, 4142638028, 4005842294, 3874862327, 3749387043, 3629125598, 3513805800, 3403172664, 3296987116, 3195024801, 3097075007, 3002939682, 2912432532, 2825378198, 2741611501, 2660976750, 2583327100, 2508523969, 2436436492, 2366941023, 2299920671, 2235264870, 2172868988, 2112633951, 2054465905, 1998275898, 1943979585, 1891496950, 1840752052, 1791672785, 1744190653, 1698240566, 1653760638, 1610692012, 1568978684, 1528567346, 1489407236, 1451449995, 1414649542, 1378961940, 1344345291, 1310759619, 1278166772, 1246530322, 1215815478, 1185988998, 1157019111, 1128875439, 1101528927, 1074951775, 1049117374, 1024000250, 999576001, 975821250, 952713592, 930231544, 908354505, 887062709, 866337187, 846159731, 826512852, 807379753, 788744290, 770590948, 752904807, 735671516, 718877270, 702508779, 686553252, 670998369, 655832263, 641043498, 626621053, 612554300, 598832991, 585447239, 572387502, 559644572, 547209555, 535073866, 523229208, 511667564, 500381186, 489362583, 478604510, 468099959, 457842149, 447824520, 438040718, 428484592, 419150186, 410031728, 401123627, 392420463, 383916983, 375608093, 367488852, 359554469, 351800293, 344221813, 336814649, 329574550, 322497385, 315579146, 308815937, 302203974, 295739578, 289419176, 283239293, 277196551, 271287663, 265509436, 259858759, 254332611, 248928047, 243642204, 238472295]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 412).prefactor = (948549944596367/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 412).cutoff/(generalMeanRows 412).c)).2 =
    (371407268779029/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 412).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 412).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 412).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 412

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 412).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 412).criticalRate j.val*(generalMeanRows 412).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 412).c*(generalMeanRows 412).criticalPoint j.val)).2-
      (generalMeanRows 412).J/2-(generalMeanRows 412).error (generalMeanGrid j.val)+
      (generalMeanRows 412).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 412).c)).2-
      (generalMeanRows 412).J/2-(generalMeanRows 412).error 4 := by
  have he : (generalMeanRows 412).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 412) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 412)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0412

/-! Kernel-checked entropy margins for general spectral rectangle 413. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0413
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4946225652, 4774213334, 4609958327, 4453017822, 4302980254, 4159462580, 4022107849, 3890583019, 3764577011, 3643798948, 3527976569, 3416854792, 3310194418, 3207770944, 3109373488, 3014803810, 2923875412, 2836412718, 2752250318, 2671232281, 2593211513, 2518049176, 2445614144, 2375782504, 2308437098, 2243467088, 2180767569, 2120239195, 2061787839, 2005324278, 1950763897, 1898026413, 1847035621, 1797719151, 1750008252, 1703837577, 1659144991, 1615871391, 1573960532, 1533358870, 1494015411, 1455881570, 1418911043, 1383059679, 1348285368, 1314547928, 1281809006, 1250031980, 1219181870, 1189225247, 1160130162, 1131866062, 1104403722, 1077715179, 1051773665, 1026553549, 1002030283, 978180343, 954981182, 932411183, 910449614, 889076580, 868272992, 848020520, 828301561, 809099208, 790397209, 772179946, 754432399, 737140122, 720289214, 703866299, 687858496, 672253405, 657039076, 642203998, 627737073, 613627604, 599865272, 586440123, 573342553, 560563291, 548093384, 535924190, 524047355, 512454813, 501138762, 490091663, 479306225, 468775393, 458492346, 448450478, 438643397, 429064914, 419709034, 410569951, 401642040, 392919847, 384398089, 376071640, 367935531, 359984942, 352215198, 344621759, 337200222, 329946311, 322855875, 315924881, 309149414, 302525669, 296049949, 289718660, 283528312, 277475507, 271556945, 265769415, 260109793, 254575040, 249162201, 243868398, 238690831]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 413).prefactor = (474485534498957/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 413).cutoff/(generalMeanRows 413).c)).2 =
    (368496058571569/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 413).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 413).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 413).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 413

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 413).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 413).criticalRate j.val*(generalMeanRows 413).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 413).c*(generalMeanRows 413).criticalPoint j.val)).2-
      (generalMeanRows 413).J/2-(generalMeanRows 413).error (generalMeanGrid j.val)+
      (generalMeanRows 413).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 413).c)).2-
      (generalMeanRows 413).J/2-(generalMeanRows 413).error 4 := by
  have he : (generalMeanRows 413).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 413) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 413)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0413

/-! Kernel-checked entropy margins for general spectral rectangle 414. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0414
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5255361059, 5087455443, 4926994389, 4773548128, 4626717508, 4486131316, 4351443899, 4222333019, 4098497939, 3979657696, 3865549539, 3755927522, 3650561221, 3549234576, 3451744828, 3357901559, 3267525803, 3180449245, 3096513475, 3015569308, 2937476163, 2862101480, 2789320194, 2719014242, 2651072108, 2585388407, 2521863493, 2460403097, 2400917999, 2343323709, 2287540182, 2233491548, 2181105861, 2130314866, 2081053778, 2033261084, 1986878348, 1941850035, 1898123343, 1855648051, 1814376370, 1774262809, 1735264046, 1697338804, 1660447747, 1624553367, 1589619887, 1555613168, 1522500621, 1490251125, 1458834948, 1428223677, 1398390144, 1369308366, 1340953483, 1313301699, 1286330227, 1260017243, 1234341829, 1209283938, 1184824341, 1160944593, 1137626991, 1114854542, 1092610923, 1070880453, 1049648060, 1028899253, 1008620096, 988797177, 969417589, 950468906, 931939157, 913816807, 896090740, 878750237, 861784959, 845184929, 828940519, 813042433, 797481690, 782249615, 767337823, 752738208, 738442929, 724444402, 710735286, 697308477, 684157095, 671274473, 658654156, 646289884, 634175591, 622305391, 610673577, 599274611, 588103116, 577153875, 566421818, 555902022, 545589705, 535480217, 525569040, 515851779, 506324160, 496982026, 487821331, 478838139, 470028616, 461389030, 452915747, 444605225, 436454016, 428458758, 420616174, 412923069, 405376329, 397972917, 390709868, 383584293, 376593371]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 414).prefactor = (2313144709905769/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 414).cutoff/(generalMeanRows 414).c)).2 =
    (84273090461937/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 414).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 414).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 414).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 414

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 414).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 414).criticalRate j.val*(generalMeanRows 414).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 414).c*(generalMeanRows 414).criticalPoint j.val)).2-
      (generalMeanRows 414).J/2-(generalMeanRows 414).error (generalMeanGrid j.val)+
      (generalMeanRows 414).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 414).c)).2-
      (generalMeanRows 414).J/2-(generalMeanRows 414).error 4 := by
  have he : (generalMeanRows 414).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 414) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 414)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0414

/-! Kernel-checked entropy margins for general spectral rectangle 415. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0415
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4943608542, 4771625487, 4607413389, 4450527635, 4300555027, 4157111041, 4019837389, 3888399820, 3762486167, 3641804568, 3526081880, 3415062229, 3308505704, 3206187166, 3107895168, 3013430965, 2922607612, 2835249139, 2751189789, 2670273327, 2592352395, 2517287926, 2444948599, 2375210336, 2307955836, 2243074150, 2180460277, 2120014798, 2061643532, 2005257216, 1950771209, 1898105217, 1847183034, 1797932300, 1750284281, 1704173659, 1659538333, 1616319240, 1574460179, 1533907657, 1494610734, 1456520884, 1419591861, 1383779579, 1349041991, 1315338982, 1282632266, 1250885288, 1220063137, 1190132453, 1161061355, 1132819359, 1105377307, 1078707302, 1052782645, 1027577769, 1003068190, 979230449, 956042060, 933481467, 911527996, 890161814, 869363884, 849115934, 829400416, 810200472, 791499903, 773283139, 755535208, 738241710, 721388790, 704963114, 688951844, 673342617, 658123525, 643283093, 628810261, 614694363, 600925117, 587492599, 574387236, 561599785, 549121326, 536943238, 525057199, 513455162, 502129353, 491072254, 480276596, 469735346, 459441699, 449389072, 439571088, 429981576, 420614559, 411464244, 402525021, 393791451, 385258263, 376920344, 368772737, 360810634, 353029368, 345424411, 337991369, 330725975, 323624085, 316681676, 309894838, 303259775, 296772795, 290430312, 284228838, 278164984, 272235453, 266437038, 260766620, 255221165, 249797720, 244493410, 239305439]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 415).prefactor = (4759319329208149/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 415).cutoff/(generalMeanRows 415).c)).2 =
    (371407268779029/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 415).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 415).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 415).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 415

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 415).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 415).criticalRate j.val*(generalMeanRows 415).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 415).c*(generalMeanRows 415).criticalPoint j.val)).2-
      (generalMeanRows 415).J/2-(generalMeanRows 415).error (generalMeanGrid j.val)+
      (generalMeanRows 415).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 415).c)).2-
      (generalMeanRows 415).J/2-(generalMeanRows 415).error 4 := by
  have he : (generalMeanRows 415).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 415) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 415)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0415

/-! Kernel-checked entropy margins for general spectral rectangle 416. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0416
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5254065918, 5086205041, 4925800498, 4772420815, 4625665300, 4485161354, 4350562071, 4221544091, 4097805666, 3979064927, 3865058315, 3755539160, 3650276395, 3549053387, 3451666874, 3357925990, 3267651380, 3180674386, 3096836301, 3015987687, 2937987742, 2862703723, 2790010409, 2719789610, 2651929709, 2586325241, 2522876500, 2461489177, 2402074024, 2344546541, 2288826686, 2234838601, 2182510364, 2131773751, 2082564021, 2034819705, 1988482420, 1943496688, 1899809773, 1857371517, 1816134201, 1776052406, 1737082881, 1699184427, 1662317783, 1626445516, 1591531928, 1557542957, 1524446091, 1492210285, 1460805884, 1430204548, 1400379186, 1371303886, 1342953862, 1315305386, 1288335742, 1262023172, 1236346827, 1211286720, 1186823689, 1162939347, 1139616053, 1116836869, 1094585530, 1072846407, 1051604483, 1030845316, 1010555019, 990720228, 971328082, 952366197, 933822645, 915685934, 897944986, 880589118, 863608028, 846991775, 830730763, 814815728, 799237720, 783988093, 769058490, 754440831, 740127301, 726110341, 712382632, 698937093, 685766863, 672865298, 660225960, 647842609, 635709192, 623819844, 612168871, 600750749, 589560117, 578591768, 567840647, 557301841, 546970580, 536842223, 526912261, 517176311, 507630105, 498269494, 489090441, 480089015, 471261389, 462603838, 454112732, 445784535, 437615803, 429603179, 421743389, 414033243, 406469629, 399049513, 391769934, 384628004, 377620904]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 416).prefactor = (4640093825441773/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 416).cutoff/(generalMeanRows 416).c)).2 =
    (212138331258571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 416).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 416).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 416).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 416

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 416).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 416).criticalRate j.val*(generalMeanRows 416).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 416).c*(generalMeanRows 416).criticalPoint j.val)).2-
      (generalMeanRows 416).J/2-(generalMeanRows 416).error (generalMeanGrid j.val)+
      (generalMeanRows 416).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 416).c)).2-
      (generalMeanRows 416).J/2-(generalMeanRows 416).error 4 := by
  have he : (generalMeanRows 416).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 416) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 416)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0416

/-! Kernel-checked entropy margins for general spectral rectangle 417. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0417
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5273254132, 5104776843, 4943769463, 4789800760, 4642470221, 4501405372, 4366259381, 4236708913, 4112452209, 3993207347, 3878710683, 3768715432, 3662990388, 3561318753, 3463497079, 3369334299, 3278650839, 3191277809, 3107056260, 3025836501, 2947477469, 2871846156, 2798817070, 2728271745, 2660098287, 2594190951, 2530449751, 2468780100, 2409092471, 2351302088, 2295328634, 2241095979, 2188531933, 2137568008, 2088139200, 2040183785, 1993643128, 1948461505, 1904585936, 1861966027, 1820553827, 1780303691, 1741172147, 1703117781, 1666101120, 1630084529, 1595032110, 1560909607, 1527684321, 1495325024, 1463801884, 1433086389, 1403151281, 1373970488, 1345519065, 1317773134, 1290709832, 1264307258, 1238544427, 1213401220, 1188858345, 1164897293, 1141500301, 1118650318, 1096330966, 1074526509, 1053221826, 1032402375, 1012054172, 992163762, 972718192, 953704994, 935112156, 916928104, 899141685, 881742143, 864719102, 848062554, 831762836, 815810621, 800196898, 784912962, 769950400, 755301077, 740957126, 726910938, 713155147, 699682623, 686486463, 673559980, 660896694, 648490325, 636334786, 624424171, 612752755, 601314978, 590105447, 579118926, 568350330, 557794717, 547447289, 537303382, 527358459, 517608113, 508048056, 498674114, 489482230, 480468452, 471628935, 462959934, 454457802, 446118985, 437940023, 429917543, 422048257, 414328960, 406756525, 399327906, 392040129, 384890294, 377875569]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 417).prefactor = (2321020337684241/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 417).cutoff/(generalMeanRows 417).c)).2 =
    (84273090461937/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 417).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 417).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 417).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 417

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 417).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 417).criticalRate j.val*(generalMeanRows 417).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 417).c*(generalMeanRows 417).criticalPoint j.val)).2-
      (generalMeanRows 417).J/2-(generalMeanRows 417).error (generalMeanGrid j.val)+
      (generalMeanRows 417).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 417).c)).2-
      (generalMeanRows 417).J/2-(generalMeanRows 417).error 4 := by
  have he : (generalMeanRows 417).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 417) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 417)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0417

/-! Kernel-checked entropy margins for general spectral rectangle 418. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0418
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5201053731, 5032317051, 4871085806, 4716927234, 4569439377, 4428248386, 4293006120, 4163388003, 4039091087, 3919832317, 3805346968, 3695387216, 3589720861, 3488130155, 3390410734, 3296370652, 3205829491, 3118617550, 3034575095, 2953551682, 2875405523, 2800002907, 2727217667, 2656930685, 2589029436, 2523407567, 2459964504, 2398605090, 2339239250, 2281781675, 2226151535, 2172272202, 2120071004, 2069478989, 2020430701, 1972863980, 1926719768, 1881941934, 1838477099, 1796274488, 1755285780, 1715464967, 1676768233, 1639153825, 1602581945, 1567014644, 1532415715, 1498750610, 1465986342, 1434091407, 1403035705, 1372790464, 1343328177, 1314622528, 1286648338, 1259381504, 1232798942, 1206878541, 1181599109, 1156940331, 1132882723, 1109407592, 1086496998, 1064133717, 1042301206, 1020983569, 1000165529, 979832398, 959970047, 940564882, 921603820, 903074262, 884964075, 867261566, 849955466, 833034911, 816489421, 800308885, 784483544, 769003977, 753861084, 739046076, 724550456, 710366012, 696484803, 682899146, 669601608, 656584994, 643842338, 631366894, 619152127, 607191702, 595479481, 584009512, 572776021, 561773407, 550996237, 540439234, 530097278, 519965395, 510038752, 500312656, 490782544, 481443981, 472292656, 463324373, 454535054, 445920729, 437477535, 429201712, 421089599, 413137631, 405342335, 397700329, 390208316, 382863085, 375661505, 368600523, 361677162, 354888521, 348231767]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 418).prefactor = (4657845559660923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 418).cutoff/(generalMeanRows 418).c)).2 =
    (41355291257289/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 418).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 418).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 418).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 418

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 418).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 418).criticalRate j.val*(generalMeanRows 418).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 418).c*(generalMeanRows 418).criticalPoint j.val)).2-
      (generalMeanRows 418).J/2-(generalMeanRows 418).error (generalMeanGrid j.val)+
      (generalMeanRows 418).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 418).c)).2-
      (generalMeanRows 418).J/2-(generalMeanRows 418).error 4 := by
  have he : (generalMeanRows 418).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 418) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 418)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0418

/-! Kernel-checked entropy margins for general spectral rectangle 419. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0419
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4987198538, 4816000535, 4652537568, 4496364737, 4347068695, 4204264893, 4067595127, 3936725337, 3811343628, 3691158500, 3575897238, 3465304463, 3359140812, 3257181748, 3159216464, 3065046896, 2974486808, 2887360967, 2803504376, 2722761575, 2644986000, 2570039383, 2497791213, 2428118225, 2360903934, 2296038205, 2233416850, 2172941259, 2114518052, 2058058761, 2003479532, 1950700846, 1899647259, 1850247167, 1802432575, 1756138890, 1711304722, 1667871705, 1625784323, 1584989748, 1545437691, 1507080261, 1469871832, 1433768921, 1398730067, 1364715727, 1331688170, 1299611380, 1268450967, 1238174082, 1208749332, 1180146710, 1152337521, 1125294314, 1098990818, 1073401887, 1048503437, 1024272398, 1000686660, 977725028, 955367178, 933593611, 912385614, 891725226, 871595198, 851978959, 832860588, 814224779, 796056815, 778342540, 761068333, 744221083, 727788169, 711757432, 696117161, 680856068, 665963272, 651428280, 637240970, 623391577, 609870673, 596669158, 583778243, 571189438, 558894539, 546885614, 535154998, 523695275, 512499272, 501560049, 490870886, 480425281, 470216935, 460239747, 450487806, 440955384, 431636928, 422527054, 413620541, 404912323, 396397487, 388071263, 379929021, 371966268, 364178637, 356561891, 349111909, 341824691, 334696345, 327723091, 320901254, 314227257, 307697624, 301308972, 295058011, 288941537, 282956434, 277099668, 271368284, 265759405, 260270230]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 419).prefactor = (4754792888713973/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 419).cutoff/(generalMeanRows 419).c)).2 =
    (96222215879131/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 419).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 419).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 419).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 419

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 419).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 419).criticalRate j.val*(generalMeanRows 419).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 419).c*(generalMeanRows 419).criticalPoint j.val)).2-
      (generalMeanRows 419).J/2-(generalMeanRows 419).error (generalMeanGrid j.val)+
      (generalMeanRows 419).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 419).c)).2-
      (generalMeanRows 419).J/2-(generalMeanRows 419).error 4 := by
  have he : (generalMeanRows 419).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 419) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 419)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0419

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock05 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 5 i) := by
  fin_cases i
  · exact EntropyRow0350.numerical
  · exact EntropyRow0351.numerical
  · exact EntropyRow0352.numerical
  · exact EntropyRow0353.numerical
  · exact EntropyRow0354.numerical
  · exact EntropyRow0355.numerical
  · exact EntropyRow0356.numerical
  · exact EntropyRow0357.numerical
  · exact EntropyRow0358.numerical
  · exact EntropyRow0359.numerical
  · exact EntropyRow0360.numerical
  · exact EntropyRow0361.numerical
  · exact EntropyRow0362.numerical
  · exact EntropyRow0363.numerical
  · exact EntropyRow0364.numerical
  · exact EntropyRow0365.numerical
  · exact EntropyRow0366.numerical
  · exact EntropyRow0367.numerical
  · exact EntropyRow0368.numerical
  · exact EntropyRow0369.numerical
  · exact EntropyRow0370.numerical
  · exact EntropyRow0371.numerical
  · exact EntropyRow0372.numerical
  · exact EntropyRow0373.numerical
  · exact EntropyRow0374.numerical
  · exact EntropyRow0375.numerical
  · exact EntropyRow0376.numerical
  · exact EntropyRow0377.numerical
  · exact EntropyRow0378.numerical
  · exact EntropyRow0379.numerical
  · exact EntropyRow0380.numerical
  · exact EntropyRow0381.numerical
  · exact EntropyRow0382.numerical
  · exact EntropyRow0383.numerical
  · exact EntropyRow0384.numerical
  · exact EntropyRow0385.numerical
  · exact EntropyRow0386.numerical
  · exact EntropyRow0387.numerical
  · exact EntropyRow0388.numerical
  · exact EntropyRow0389.numerical
  · exact EntropyRow0390.numerical
  · exact EntropyRow0391.numerical
  · exact EntropyRow0392.numerical
  · exact EntropyRow0393.numerical
  · exact EntropyRow0394.numerical
  · exact EntropyRow0395.numerical
  · exact EntropyRow0396.numerical
  · exact EntropyRow0397.numerical
  · exact EntropyRow0398.numerical
  · exact EntropyRow0399.numerical
  · exact EntropyRow0400.numerical
  · exact EntropyRow0401.numerical
  · exact EntropyRow0402.numerical
  · exact EntropyRow0403.numerical
  · exact EntropyRow0404.numerical
  · exact EntropyRow0405.numerical
  · exact EntropyRow0406.numerical
  · exact EntropyRow0407.numerical
  · exact EntropyRow0408.numerical
  · exact EntropyRow0409.numerical
  · exact EntropyRow0410.numerical
  · exact EntropyRow0411.numerical
  · exact EntropyRow0412.numerical
  · exact EntropyRow0413.numerical
  · exact EntropyRow0414.numerical
  · exact EntropyRow0415.numerical
  · exact EntropyRow0416.numerical
  · exact EntropyRow0417.numerical
  · exact EntropyRow0418.numerical
  · exact EntropyRow0419.numerical
end SingularValueBounds.KL.Certificates
