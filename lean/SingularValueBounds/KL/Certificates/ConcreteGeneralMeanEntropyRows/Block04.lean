import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 280. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0280
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4818944753, 4643836770, 4476803254, 4317379387, 4165133222, 4019662820, 3880593696, 3747576524, 3620285090, 3498414438, 3381679200, 3269812088, 3162562521, 3059695386, 2960989896, 2866238564, 2775246254, 2687829314, 2603814787, 2523039677, 2445350284, 2370601581, 2298656645, 2229386136, 2162667804, 2098386044, 2036431474, 1976700551, 1919095211, 1863522534, 1809894436, 1758127374, 1708142083, 1659863320, 1613219630, 1568143130, 1524569299, 1482436792, 1441687254, 1402265162, 1364117655, 1327194399, 1291447440, 1256831079, 1223301746, 1190817891, 1159339872, 1128829853, 1099251715, 1070570960, 1042754630, 1015771224, 989590630, 964184047, 939523922, 915583889, 892338704, 869764195, 847837208, 826535552, 805837958, 785724034, 766174217, 747169739, 728692588, 710725472, 693251781, 676255564, 659721489, 643634821, 627981393, 612747577, 597920263, 583486836, 569435152, 555753518, 542430669, 529455757, 516818323, 504508289, 492515935, 480831888, 469447104, 458352858, 447540725, 437002574, 426730551, 416717071, 406954803, 397436665, 388155808, 379105611, 370279672, 361671797, 353275992, 345086457, 337097577, 329303917, 321700213, 314281365, 307042433, 299978631, 293085318, 286357996, 279792306, 273384017, 267129027, 261023357, 255063145, 249244643, 243564214, 238018326, 232603550, 227316556, 222154109, 217113067, 212190377, 207383071, 202688266, 198103159, 193625024]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 280).prefactor = (2450754123936641/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 280).cutoff/(generalMeanRows 280).c)).2 =
    (178128549058887/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 280).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 280).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 280).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 280

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 280).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 280).criticalRate j.val*(generalMeanRows 280).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 280).c*(generalMeanRows 280).criticalPoint j.val)).2-
      (generalMeanRows 280).J/2-(generalMeanRows 280).error (generalMeanGrid j.val)+
      (generalMeanRows 280).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 280).c)).2-
      (generalMeanRows 280).J/2-(generalMeanRows 280).error 4 := by
  have he : (generalMeanRows 280).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 280) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 280)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0280

/-! Kernel-checked entropy margins for general spectral rectangle 281. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0281
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4812475583, 4637644629, 4470867315, 4311680570, 4159654048, 4014387277, 3875507114, 3742665468, 3615537253, 3493818550, 3377224940, 3265490006, 3158363968, 3055612443, 2957015316, 2862365717, 2771469072, 2684142248, 2600212761, 2519518050, 2441904810, 2367228377, 2295352165, 2226147134, 2159491314, 2095269353, 2033372101, 1973696227, 1916143860, 1860622256, 1807043489, 1755324165, 1705385149, 1657151319, 1610551330, 1565517397, 1521985089, 1479893141, 1439183274, 1399800028, 1361690604, 1324804720, 1289094470, 1254514199, 1221020376, 1188571485, 1157127914, 1126651857, 1097107217, 1068459518, 1040675821, 1013724643, 987575885, 962200760, 937571726, 913662426, 890447626, 867903161, 846005881, 824733602, 804065061, 783979867, 764458461, 745482079, 727032710, 709093062, 691646529, 674677160, 658169624, 642109187, 626481681, 611273480, 596471474, 582063048, 568036058, 554378810, 541080043, 528128905, 515514941, 503228070, 491258574, 479597080, 468234546, 457162244, 446371754, 435854944, 425603961, 415611220, 405869393, 396371397, 387110386, 378079741, 369273060, 360684150, 352307021, 344135873, 336165094, 328389251, 320803080, 313401486, 306179529, 299132426, 292255539, 285544373, 278994569, 272601901, 266362269, 260271696, 254326322, 248522404, 242856307, 237324501, 231923560, 226650158, 221501061, 216473132, 211563319, 206768659, 202086271, 197513355, 193047189]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 281).prefactor = (4885466664667211/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 281).cutoff/(generalMeanRows 281).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 281).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 281).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 281).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 281

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 281).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 281).criticalRate j.val*(generalMeanRows 281).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 281).c*(generalMeanRows 281).criticalPoint j.val)).2-
      (generalMeanRows 281).J/2-(generalMeanRows 281).error (generalMeanGrid j.val)+
      (generalMeanRows 281).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 281).c)).2-
      (generalMeanRows 281).J/2-(generalMeanRows 281).error 4 := by
  have he : (generalMeanRows 281).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 281) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 281)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0281

/-! Kernel-checked entropy margins for general spectral rectangle 282. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0282
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4820918486, 4645780812, 4478710908, 4319244889, 4166951655, 4021430031, 3882306219, 3749231519, 3621880273, 3499948029, 3383149870, 3271218911, 3163904934, 3060973143, 2962203040, 2867387389, 2776331277, 2688851249, 2604774518, 2523938238, 2446188835, 2371381392, 2299379081, 2230052638, 2163279879, 2098945248, 2036939405, 1977158837, 1919505501, 1863886491, 1810213727, 1758403668, 1708377040, 1660058590, 1613376847, 1568263907, 1524655227, 1482489434, 1441708146, 1402255807, 1364079524, 1327128928, 1291356030, 1256715092, 1223162508, 1190656689, 1159157955, 1128628431, 1099031958, 1070334000, 1042501560, 1015503099, 989308467, 963888824, 939216582, 915265336, 892009808, 869425791, 847490095, 826180497, 805475696, 785355264, 765799611, 746789937, 728308200, 710337079, 692859939, 675860799, 659324302, 643235689, 627580767, 612345885, 597517911, 583084207, 569032608, 555351401, 542029302, 529055443, 516419349, 504110922, 492120428, 480438475, 469056006, 457964280, 447154859, 436619599, 426350631, 416340360, 406581442, 397066783, 387789525, 378743036, 369920905, 361316927, 352925100, 344739617, 336754855, 328965370, 321365890, 313951310, 306716684, 299657218, 292768266, 286045326, 279484031, 273080148, 266829569, 260728311, 254772507, 248958407, 243282369, 237740858, 232330442, 227047788, 221889658, 216852908, 211934481, 207131410, 202440807, 197859868, 193385867]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 282).prefactor = (4894037621675089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 282).cutoff/(generalMeanRows 282).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 282).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 282).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 282).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 282

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 282).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 282).criticalRate j.val*(generalMeanRows 282).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 282).c*(generalMeanRows 282).criticalPoint j.val)).2-
      (generalMeanRows 282).J/2-(generalMeanRows 282).error (generalMeanGrid j.val)+
      (generalMeanRows 282).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 282).c)).2-
      (generalMeanRows 282).J/2-(generalMeanRows 282).error 4 := by
  have he : (generalMeanRows 282).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 282) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 282)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0282

/-! Kernel-checked entropy margins for general spectral rectangle 283. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0283
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4817647877, 4642650495, 4475710384, 4316364536, 4164182655, 4018764304, 3879736359, 3746750739, 3619482356, 3497627277, 3380901062, 3269037267, 3161786072, 3058913054, 2960198051, 2865434137, 2774426683, 2686992496, 2602959027, 2522163649, 2444452989, 2369682314, 2297714962, 2228421825, 2161680857, 2097376633, 2035399929, 1975647340, 1918020921, 1862427854, 1808780141, 1756994314, 1706991168, 1658695509, 1612035924, 1566944559, 1523356915, 1481211662, 1440450455, 1401017771, 1362860749, 1325929047, 1290174699, 1255551992, 1222017339, 1189529168, 1158047815, 1127535420, 1097955837, 1069274541, 1041458543, 1014476316, 988297714, 962893908, 938237313, 914301530, 891061287, 868492378, 846571619, 825276788, 804586587, 784480592, 764939212, 745943650, 727475866, 709518538, 692055033, 675069371, 658546195, 642470746, 626828832, 611606803, 596791526, 582370364, 568331153, 554662178, 541352157, 528390221, 515765896, 503469085, 491490052, 479819407, 468448093, 457367369, 446568799, 436044236, 425785816, 415785940, 406037268, 396532706, 387265395, 378228706, 369416227, 360821755, 352439289, 344263021, 336287330, 328506774, 320916082, 313510150, 306284031, 299232934, 292352215, 285637371, 279084039, 272687984, 266445102, 260351409, 254403043, 248596252, 242927396, 237392943, 231989461, 226713619, 221562180, 216532002, 211620030, 206823297, 202138917, 197564089, 193096086]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 283).prefactor = (977197247949593/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 283).cutoff/(generalMeanRows 283).c)).2 =
    (177010397269747/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 283).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 283).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 283).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 283

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 283).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 283).criticalRate j.val*(generalMeanRows 283).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 283).c*(generalMeanRows 283).criticalPoint j.val)).2-
      (generalMeanRows 283).J/2-(generalMeanRows 283).error (generalMeanGrid j.val)+
      (generalMeanRows 283).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 283).c)).2-
      (generalMeanRows 283).J/2-(generalMeanRows 283).error 4 := by
  have he : (generalMeanRows 283).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 283) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 283)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0283

/-! Kernel-checked entropy margins for general spectral rectangle 284. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0284
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4821880592, 4646729460, 4479642678, 4320156831, 4167841246, 4022295132, 3883145039, 3750042580, 3622662381, 3500700241, 3383871473, 3271909395, 3164563972, 3061600571, 2962798837, 2867951666, 2776864254, 2689353249, 2605245949, 2524379586, 2446600650, 2371764282, 2299733701, 2230379684, 2163580079, 2099219358, 2037188202, 1977383115, 1919706066, 1864064156, 1810369309, 1758537983, 1708490905, 1660152815, 1613452236, 1568321253, 1524695314, 1482513033, 1441716014, 1402248685, 1364058139, 1327093989, 1291308228, 1256655102, 1223090986, 1190574271, 1159065259, 1128526057, 1098920486, 1070213990, 1042373553, 1015367620, 989166018, 963739892, 939061634, 915104822, 891844160, 869255423, 847315404, 826001865, 805293486, 785169826, 765611277, 746599026, 728115016, 710141911, 692663063, 675662477, 659124784, 643035212, 627379555, 612144152, 597315858, 582882027, 568830480, 555149496, 541827781, 528854457, 516219041, 503911425, 491921868, 480240969, 468859665, 457769206, 446961147, 436427338, 426159905, 416151244, 406394007, 396881094, 387605641, 378561013, 369740791, 361138768, 352748937, 344565486, 336582788, 328795396, 321198035, 313785595, 306553128, 299495836, 292609071, 285888328, 279329238, 272927564, 266679196, 260580150, 254626558, 248814665, 243140829, 237601513, 232193284, 226912806, 221756842, 216722244, 211805956, 207005009, 202316514, 197737666, 193265738]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 284).prefactor = (4890278996228833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 284).cutoff/(generalMeanRows 284).c)).2 =
    (177010397269747/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 284).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 284).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 284).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 284

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 284).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 284).criticalRate j.val*(generalMeanRows 284).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 284).c*(generalMeanRows 284).criticalPoint j.val)).2-
      (generalMeanRows 284).J/2-(generalMeanRows 284).error (generalMeanGrid j.val)+
      (generalMeanRows 284).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 284).c)).2-
      (generalMeanRows 284).J/2-(generalMeanRows 284).error 4 := by
  have he : (generalMeanRows 284).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 284) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 284)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0284

/-! Kernel-checked entropy margins for general spectral rectangle 285. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0285
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4747418252, 4572730448, 4406115788, 4247110700, 4095284323, 3950235660, 3811591032, 3679001802, 3552142336, 3430708157, 3314414291, 3202993761, 3096196228, 2993786751, 2895544662, 2801262538, 2710745261, 2623809155, 2540281203, 2459998315, 2382806667, 2308561085, 2237124479, 2168367317, 2102167144, 2038408135, 1976980678, 1917780989, 1860710753, 1805676798, 1752590776, 1701368884, 1651931590, 1604203385, 1558112547, 1513590928, 1470573743, 1428999385, 1388809242, 1349947535, 1312361154, 1275999517, 1240814430, 1206759958, 1173792302, 1141869686, 1110952249, 1081001946, 1051982449, 1023859061, 996598631, 970169473, 944541292, 919685115, 895573223, 872179087, 849477311, 827443575, 806054582, 785288007, 765122453, 745537402, 726513176, 708030897, 690072445, 672620429, 655658145, 639169552, 623139236, 607552382, 592394748, 577652639, 563312880, 549362797, 535790190, 522583313, 509730859, 497221933, 485046039, 473193064, 461653255, 450417212, 439475867, 428820473, 418442587, 408334063, 398487036, 388893910, 379547348, 370440263, 361565807, 352917358, 344488517, 336273096, 328265108, 320458764, 312848459, 305428772, 298194453, 291140419, 284261750, 277553676, 271011581, 264630988, 258407561, 252337095, 246415515, 240638867, 235003320, 229505155, 224140763, 218906645, 213799404, 208815741, 203952456, 199206440, 194574675, 190054229, 185642253, 181335981, 177132725]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 285).prefactor = (305675419952237/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 285).cutoff/(generalMeanRows 285).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 285).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 285).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 285).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 285

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 285).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 285).criticalRate j.val*(generalMeanRows 285).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 285).c*(generalMeanRows 285).criticalPoint j.val)).2-
      (generalMeanRows 285).J/2-(generalMeanRows 285).error (generalMeanGrid j.val)+
      (generalMeanRows 285).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 285).c)).2-
      (generalMeanRows 285).J/2-(generalMeanRows 285).error 4 := by
  have he : (generalMeanRows 285).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 285) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 285)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0285

/-! Kernel-checked entropy margins for general spectral rectangle 286. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0286
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4751597746, 4576756153, 4409994810, 4250849738, 4098889698, 3953713338, 3814946650, 3682240693, 3555269543, 3433728457, 3317332209, 3205813588, 3098922033, 2996422397, 2898093819, 2803728692, 2713131726, 2626119084, 2542517595, 2462164029, 2384904424, 2310593478, 2239093981, 2170276287, 2104017833, 2040202693, 1978721157, 1919469350, 1862348871, 1807266465, 1754133708, 1702866722, 1653385905, 1605615681, 1559484266, 1514923451, 1471868395, 1430257436, 1390031911, 1351135991, 1313516520, 1277122871, 1241906809, 1207822356, 1174825676, 1142874956, 1111930301, 1081953630, 1052908585, 1024760438, 997476009, 971023583, 945372840, 920494780, 896361661, 872946929, 850225167, 828172034, 806764210, 785979353, 765796045, 746193752, 727152778, 708654228, 690679966, 673212585, 656235368, 639732259, 623687830, 608087254, 592916276, 578161188, 563808805, 549846441, 536261885, 523043381, 510179612, 497659673, 485473060, 473609650, 462059682, 450813747, 439862770, 429197994, 418810972, 408693549, 398837853, 389236281, 379881491, 370766389, 361884119, 353228057, 344791795, 336569142, 328554104, 320740887, 313123883, 305697663, 298456975, 291396731, 284512006, 277798027, 271250172, 264863962, 258635055, 252559245, 246632452, 240850719, 235210211, 229707205, 224338090, 219099365, 213987627, 208999577, 204132010, 199381816, 194745973, 190221547, 185805687, 181495624, 177288668]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 286).prefactor = (305944528088669/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 286).cutoff/(generalMeanRows 286).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 286).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 286).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 286).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 286

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 286).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 286).criticalRate j.val*(generalMeanRows 286).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 286).c*(generalMeanRows 286).criticalPoint j.val)).2-
      (generalMeanRows 286).J/2-(generalMeanRows 286).error (generalMeanGrid j.val)+
      (generalMeanRows 286).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 286).c)).2-
      (generalMeanRows 286).J/2-(generalMeanRows 286).error 4 := by
  have he : (generalMeanRows 286).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 286) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 286)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0286

/-! Kernel-checked entropy margins for general spectral rectangle 287. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0287
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4759967778, 4584818198, 4417763101, 4258337692, 4106109971, 3960677881, 3821666753, 3688727031, 3561532219, 3439777036, 3323175754, 3211460690, 3104380844, 3001700654, 2903198868, 2808667515, 2717910960, 2630745044, 2546996290, 2466501178, 2389105479, 2314663634, 2243038189, 2174099271, 2107724102, 2043796550, 1982206713, 1922850532, 1865629435, 1810450000, 1757223649, 1705866355, 1656298376, 1608444004, 1562231328, 1517592018, 1474461120, 1432776862, 1392480480, 1353516043, 1315830305, 1279372548, 1244094452, 1209949958, 1176895154, 1144888152, 1113888987, 1083859512, 1054763304, 1026565574, 999233082, 972734060, 947038132, 922116250, 897940619, 874484642, 851722856, 829630875, 808185341, 787363871, 767145010, 747508187, 728433672, 709902536, 691896612, 674398462, 657391340, 640859160, 624786469, 609158412, 593960709, 579179630, 564801966, 550815006, 537206520, 523964732, 511078303, 498536310, 486328231, 474443922, 462873609, 451607864, 440637597, 429954035, 419548716, 409413471, 399540414, 389921928, 380550659, 371419501, 362521585, 353850275, 345399153, 337162015, 329132858, 321305878, 313675456, 306236156, 298982713, 291910032, 285013179, 278287373, 271727984, 265330525, 259090646, 253004133, 247066900, 241274982, 235624538, 230111838, 224733266, 219485312, 214364570, 209367734, 204491593, 199733031, 195089022, 190556626, 186132988, 181815333, 177600965]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 287).prefactor = (1225933821264233/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 287).cutoff/(generalMeanRows 287).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 287).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 287).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 287).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 287

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 287).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 287).criticalRate j.val*(generalMeanRows 287).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 287).c*(generalMeanRows 287).criticalPoint j.val)).2-
      (generalMeanRows 287).J/2-(generalMeanRows 287).error (generalMeanGrid j.val)+
      (generalMeanRows 287).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 287).c)).2-
      (generalMeanRows 287).J/2-(generalMeanRows 287).error 4 := by
  have he : (generalMeanRows 287).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 287) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 287)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0287

/-! Kernel-checked entropy margins for general spectral rectangle 288. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0288
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5320411858, 5153660274, 4994362616, 4842082075, 4696413223, 4556979279, 4423429652, 4295437755, 4172699027, 4054929165, 3941862517, 3833250637, 3728860964, 3628475628, 3531890367, 3438913523, 3349365145, 3263076150, 3179887562, 3099649817, 3022222111, 2947471815, 2875273922, 2805510548, 2738070461, 2672848652, 2609745935, 2548668576, 2489527950, 2432240220, 2376726045, 2322910297, 2270721811, 2220093138, 2170960330, 2123262726, 2076942759, 2031945776, 1988219865, 1945715700, 1904386390, 1864187340, 1825076123, 1787012353, 1749957577, 1713875164, 1678730202, 1644489409, 1611121039, 1578594802, 1546881785, 1515954375, 1485786194, 1456352032, 1427627782, 1399590390, 1372217793, 1345488871, 1319383398, 1293881997, 1268966096, 1244617888, 1220820292, 1197556917, 1174812028, 1152570516, 1130817861, 1109540112, 1088723852, 1068356177, 1048424670, 1028917379, 1009822793, 991129822, 972827780, 954906364, 937355637, 920166012, 903328236, 886833372, 870672793, 854838159, 839321410, 824114753, 809210650, 794601807, 780281163, 766241883, 752477344, 738981133, 725747029, 712769005, 700041214, 687557983, 675313807, 663303343, 651521401, 639962943, 628623069, 617497022, 606580175, 595868028, 585356205, 575040449, 564916616, 554980673, 545228692, 535656849, 526261418, 517038769, 507985363, 499097752, 490372573, 481806546, 473396472, 465139231, 457031777, 449071137, 441254410, 433578762, 426041427]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 288).prefactor = (4650376221336851/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 288).cutoff/(generalMeanRows 288).c)).2 =
    (223363845847411/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 288).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 288).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 288).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 288

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 288).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 288).criticalRate j.val*(generalMeanRows 288).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 288).c*(generalMeanRows 288).criticalPoint j.val)).2-
      (generalMeanRows 288).J/2-(generalMeanRows 288).error (generalMeanGrid j.val)+
      (generalMeanRows 288).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 288).c)).2-
      (generalMeanRows 288).J/2-(generalMeanRows 288).error 4 := by
  have he : (generalMeanRows 288).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 288) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 288)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0288

/-! Kernel-checked entropy margins for general spectral rectangle 289. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0289
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4896536523, 4720898938, 4553342803, 4393401648, 4240642067, 4094660835, 3955082338, 3821556271, 3693755564, 3571374526, 3454127163, 3341745655, 3233978980, 3130591658, 3031362614, 2936084130, 2844560903, 2756609163, 2672055883, 2590738039, 2512501937, 2437202595, 2364703160, 2294874390, 2227594155, 2162746989, 2100223668, 2039920822, 1981740570, 1925590189, 1871381799, 1819032068, 1768461949, 1719596420, 1672364252, 1626697787, 1582532734, 1539807974, 1498465382, 1458449658, 1419708167, 1382190796, 1345849808, 1310639720, 1276517172, 1243440821, 1211371225, 1180270749, 1150103461, 1120835053, 1092432746, 1064865217, 1038102522, 1012116026, 986878335, 962363234, 938545629, 915401488, 892907793, 871042484, 849784416, 829113316, 809009734, 789455013, 770431241, 751921223, 733908445, 716377039, 699311760, 682697948, 666521509, 650768884, 635427028, 620483384, 605925864, 591742824, 577923050, 564455734, 551330458, 538537180, 526066211, 513908207, 502054151, 490495337, 479223363, 468230113, 457507745, 447048686, 436845612, 426891445, 417179341, 407702679, 398455054, 389430268, 380622322, 372025406, 363633898, 355442348, 347445478, 339638175, 332015481, 324572589, 317304842, 310207719, 303276836, 296507941, 289896906, 283439725, 277132508, 270971481, 264952976, 259073432, 253329387, 247717480, 242234444, 236877103, 231642370, 226527243, 221528804, 216644214, 211870711]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 289).prefactor = (491626410043127/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 289).cutoff/(generalMeanRows 289).c)).2 =
    (36690950971171/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 289).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 289).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 289).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 289

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 289).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 289).criticalRate j.val*(generalMeanRows 289).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 289).c*(generalMeanRows 289).criticalPoint j.val)).2-
      (generalMeanRows 289).J/2-(generalMeanRows 289).error (generalMeanGrid j.val)+
      (generalMeanRows 289).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 289).c)).2-
      (generalMeanRows 289).J/2-(generalMeanRows 289).error 4 := by
  have he : (generalMeanRows 289).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 289) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 289)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0289

/-! Kernel-checked entropy margins for general spectral rectangle 290. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0290
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4930572411, 4753713966, 4584993147, 4423940239, 4270118824, 4123122874, 3982574166, 3848119957, 3719430906, 3596199196, 3478136845, 3364974172, 3256458409, 3152352441, 3052433654, 2956492889, 2864333482, 2775770388, 2690629377, 2608746292, 2529966370, 2454143621, 2381140242, 2310826091, 2243078190, 2177780271, 2114822350, 2054100337, 1995515674, 1938974991, 1884389797, 1831676183, 1780754551, 1731549357, 1683988877, 1638004984, 1593532939, 1550511199, 1508881234, 1468587360, 1429576577, 1391798422, 1355204828, 1319749993, 1285390260, 1252083994, 1219791482, 1188474826, 1158097845, 1128625991, 1100026260, 1072267108, 1045318386, 1019151257, 993738139, 969052633, 945069471, 921764456, 899114406, 877097111, 855691279, 834876493, 814633171, 794942525, 775786518, 757147837, 739009851, 721356585, 704172685, 687443390, 671154509, 655292387, 639843889, 624796372, 610137662, 595856036, 581940200, 568379273, 555162763, 542280558, 529722904, 517480390, 505543935, 493904777, 482554451, 471484786, 460687888, 450156127, 439882131, 429858773, 420079160, 410536625, 401224720, 392137203, 383268032, 374611360, 366161522, 357913032, 349860576, 341999004, 334323324, 326828698, 319510432, 312363976, 305384917, 298568971, 291911983, 285409918, 279058860, 272855008, 266794668, 260874254, 255090283, 249439367, 243918219, 238523639, 233252519, 228101837, 223068653, 218150110, 213343427]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 290).prefactor = (4950437114822699/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 290).cutoff/(generalMeanRows 290).c)).2 =
    (36690950971171/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 290).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 290).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 290).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 290

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 290).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 290).criticalRate j.val*(generalMeanRows 290).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 290).c*(generalMeanRows 290).criticalPoint j.val)).2-
      (generalMeanRows 290).J/2-(generalMeanRows 290).error (generalMeanGrid j.val)+
      (generalMeanRows 290).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 290).c)).2-
      (generalMeanRows 290).J/2-(generalMeanRows 290).error 4 := by
  have he : (generalMeanRows 290).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 290) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 290)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0290

/-! Kernel-checked entropy margins for general spectral rectangle 291. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0291
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5262065066, 5094461134, 4934370865, 4781354586, 4635004184, 4494940349, 4360810115, 4232284651, 4109057281, 3990841700, 3877370362, 3768393023, 3663675419, 3562998062, 3466155148, 3372953557, 3283211938, 3196759877, 3113437127, 3033092910, 2955585261, 2880780440, 2808552378, 2738782171, 2671357611, 2606172753, 2543127512, 2482127292, 2423082638, 2365908919, 2310526026, 2256858096, 2204833253, 2154383368, 2105443835, 2057953361, 2011853768, 1967089816, 1923609026, 1881361526, 1840299898, 1800379039, 1761556029, 1723790012, 1687042077, 1651275149, 1616453893, 1582544613, 1549515169, 1517334884, 1485974475, 1455405971, 1425602648, 1396538960, 1368190481, 1340533840, 1313546675, 1287207574, 1261496029, 1236392391, 1211877824, 1187934269, 1164544397, 1141691581, 1119359857, 1097533894, 1076198959, 1055340893, 1034946081, 1015001426, 995494325, 976412645, 957744703, 939479242, 921605414, 904112760, 886991194, 870230982, 853822733, 837757376, 822026152, 806620597, 791532531, 776754045, 762277489, 748095461, 734200797, 720586562, 707246040, 694172722, 681360302, 668802667, 656493888, 644428215, 632600068, 621004032, 609634848, 598487412, 587556763, 576838081, 566326682, 556018013, 545907645, 535991270, 526264696, 516723847, 507364750, 498183541, 489176455, 480339825, 471670078, 463163732, 454817394, 446627754, 438591588, 430705747, 422967162, 415372838, 407919853, 400605354, 393426556]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 291).prefactor = (18724574776919/4000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 291).cutoff/(generalMeanRows 291).c)).2 =
    (438727649027743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 291).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 291).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 291).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 291

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 291).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 291).criticalRate j.val*(generalMeanRows 291).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 291).c*(generalMeanRows 291).criticalPoint j.val)).2-
      (generalMeanRows 291).J/2-(generalMeanRows 291).error (generalMeanGrid j.val)+
      (generalMeanRows 291).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 291).c)).2-
      (generalMeanRows 291).J/2-(generalMeanRows 291).error 4 := by
  have he : (generalMeanRows 291).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 291) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 291)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0291

/-! Kernel-checked entropy margins for general spectral rectangle 292. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0292
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5296879549, 5128166728, 4967017283, 4812988629, 4665669954, 4524679439, 4389661783, 4260285978, 4136243320, 4017245610, 3903023531, 3793325184, 3687914755, 3586571305, 3489087666, 3395269441, 3304934080, 3217910041, 3134036018, 3053160234, 2975139784, 2899840045, 2827134113, 2756902297, 2689031648, 2623415519, 2559953163, 2498549357, 2439114057, 2381562070, 2325812756, 2271789752, 2219420706, 2168637039, 2119373716, 2071569038, 2025164445, 1980104329, 1936335865, 1893808850, 1852475553, 1812290573, 1773210705, 1735194824, 1698203759, 1662200193, 1627148555, 1593014927, 1559766955, 1527373762, 1495805869, 1465035120, 1435034614, 1405778638, 1377242601, 1349402980, 1322237265, 1295723900, 1269842245, 1244572518, 1219895760, 1195793791, 1172249169, 1149245156, 1126765683, 1104795316, 1083319226, 1062323161, 1041793414, 1021716803, 1002080640, 982872714, 964081262, 945694954, 927702871, 910094484, 892859639, 875988540, 859471731, 843300084, 827464780, 811957300, 796769410, 781893147, 767320812, 753044954, 739058362, 725354054, 711925268, 698765456, 685868267, 673227549, 660837334, 648691833, 636785429, 625112672, 613668269, 602447080, 591444112, 580654514, 570073571, 559696698, 549519438, 539537455, 529746530, 520142557, 510721539, 501479586, 492412908, 483517814, 474790706, 466228081, 457826523, 449582700, 441493365, 433555350, 425765566, 418120997, 410618702, 403255809, 396029515]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 292).prefactor = (2356057364292943/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 292).cutoff/(generalMeanRows 292).c)).2 =
    (438727649027743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 292).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 292).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 292).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 292

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 292).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 292).criticalRate j.val*(generalMeanRows 292).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 292).c*(generalMeanRows 292).criticalPoint j.val)).2-
      (generalMeanRows 292).J/2-(generalMeanRows 292).error (generalMeanGrid j.val)+
      (generalMeanRows 292).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 292).c)).2-
      (generalMeanRows 292).J/2-(generalMeanRows 292).error 4 := by
  have he : (generalMeanRows 292).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 292) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 292)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0292

/-! Kernel-checked entropy margins for general spectral rectangle 293. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0293
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5534503540, 5358160127, 5189766574, 5028856093, 4874995419, 4727781891, 4586840828, 4451823193, 4322403488, 4198277858, 4079162381, 3964791521, 3854916718, 3749305117, 3647738406, 3550011748, 3455932817, 3365320908, 3278006125, 3193828628, 3112637952, 3034292366, 2958658295, 2885609779, 2815027973, 2746800688, 2680821962, 2616991666, 2555215136, 2495402830, 2437470013, 2381336460, 2326926183, 2274167174, 2222991167, 2173333414, 2125132476, 2078330034, 2032870701, 1988701856, 1945773485, 1904038031, 1863450252, 1823967099, 1785547582, 1748152664, 1711745151, 1676289587, 1641752163, 1608100626, 1575304198, 1543333490, 1512160435, 1481758215, 1452101194, 1423164859, 1394925758, 1367361448, 1340450444, 1314172165, 1288506893, 1263435727, 1238940542, 1215003953, 1191609274, 1168740486, 1146382205, 1124519650, 1103138612, 1082225431, 1061766965, 1041750571, 1022164074, 1002995752, 984234313, 965868871, 947888934, 930284380, 913045447, 896162710, 879627069, 863429735, 847562218, 832016308, 816784071, 801857830, 787230159, 772893868, 758841998, 745067808, 731564767, 718326546, 705347008, 692620203, 680140357, 667901871, 655899305, 644127382, 632580973, 621255098, 610144916, 599245722, 588552941, 578062123, 567768940, 557669180, 547758743, 538033639, 528489982, 519123985, 509931961, 500910316, 492055547, 483364241, 474833066, 466458776, 458238204, 450168257, 442245920, 434468249, 426832369]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 293).prefactor = (1226642807504379/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 293).cutoff/(generalMeanRows 293).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 293).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 293).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 293).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 293

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 293).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 293).criticalRate j.val*(generalMeanRows 293).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 293).c*(generalMeanRows 293).criticalPoint j.val)).2-
      (generalMeanRows 293).J/2-(generalMeanRows 293).error (generalMeanGrid j.val)+
      (generalMeanRows 293).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 293).c)).2-
      (generalMeanRows 293).J/2-(generalMeanRows 293).error 4 := by
  have he : (generalMeanRows 293).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 293) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 293)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0293

/-! Kernel-checked entropy margins for general spectral rectangle 294. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0294
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5571764406, 5394233767, 5224706510, 5062712704, 4907816168, 4759611529, 4617721585, 4481794948, 4351503929, 4226542628, 4106625210, 3991484351, 3880869820, 3774547193, 3672296687, 3573912087, 3479199772, 3387977822, 3300075195, 3215330976, 3133593686, 3054720641, 2978577366, 2905037053, 2833980058, 2765293434, 2698870509, 2634610478, 2572418039, 2512203049, 2453880201, 2397368730, 2342592138, 2289477931, 2237957383, 2187965311, 2139439862, 2092322324, 2046556937, 2002090727, 1958873342, 1916856905, 1875995871, 1836246898, 1797568723, 1759922046, 1723269420, 1687575152, 1652805206, 1618927112, 1585909882, 1553723933, 1522341007, 1491734104, 1461877419, 1432746270, 1404317050, 1376567165, 1349474983, 1323019787, 1297181724, 1271941767, 1247281669, 1223183928, 1199631745, 1176608994, 1154100186, 1132090442, 1110565457, 1089511478, 1068915277, 1048764123, 1029045761, 1009748389, 990860638, 972371552, 954270565, 936547490, 919192496, 902196096, 885549129, 869242748, 853268403, 837617831, 822283044, 807256312, 792530160, 778097351, 763950877, 750083953, 736490003, 723162656, 710095734, 697283246, 684719380, 672398498, 660315126, 648463949, 636839804, 625437678, 614252697, 603280124, 592515354, 581953907, 571591426, 561423669, 551446511, 541655933, 532048023, 522618970, 513365061, 504282678, 495368295, 486618475, 478029865, 469599195, 461323277, 453199000, 445223326, 437393292, 429706005]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 294).prefactor = (4939604562166251/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 294).cutoff/(generalMeanRows 294).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 294).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 294).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 294).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 294

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 294).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 294).criticalRate j.val*(generalMeanRows 294).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 294).c*(generalMeanRows 294).criticalPoint j.val)).2-
      (generalMeanRows 294).J/2-(generalMeanRows 294).error (generalMeanGrid j.val)+
      (generalMeanRows 294).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 294).c)).2-
      (generalMeanRows 294).J/2-(generalMeanRows 294).error 4 := by
  have he : (generalMeanRows 294).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 294) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 294)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0294

/-! Kernel-checked entropy margins for general spectral rectangle 295. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0295
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5327305011, 5149353583, 4979468672, 4817180759, 4662053849, 4513682551, 4371689463, 4235722829, 4105454447, 3980577766, 3860806185, 3745871507, 3635522533, 3529523793, 3427654380, 3329706898, 3235486488, 3144809947, 3057504911, 2973409112, 2892369691, 2814242566, 2738891848, 2666189305, 2596013860, 2528251136, 2462793027, 2399537303, 2338387242, 2279251289, 2222042742, 2166679451, 2113083551, 2061181197, 2010902333, 1962180464, 1914952451, 1869158314, 1824741051, 1781646467, 1739823016, 1699221651, 1659795683, 1621500651, 1584294200, 1548135961, 1512987449, 1478811956, 1445574456, 1413241517, 1381781215, 1351163054, 1321357891, 1292337866, 1264076337, 1236547813, 1209727898, 1183593235, 1158121453, 1133291118, 1109081684, 1085473453, 1062447529, 1039985780, 1018070802, 996685883, 975814968, 955442631, 935554041, 916134938, 897171604, 878650836, 860559927, 842886638, 825619181, 808746195, 792256729, 776140222, 760386489, 744985699, 729928364, 715205324, 700807728, 686727027, 672954958, 659483531, 646305020, 633411950, 620797089, 608453434, 596374207, 584552842, 572982976, 561658446, 550573275, 539721668, 529098006, 518696835, 508512865, 498540960, 488776133, 479213542, 469848482, 460676384, 451692805, 442893427, 434274051, 425830597, 417559090, 409455669, 401516572, 393738139, 386116808, 378649108, 371331662, 364161177, 357134447, 350248346, 343499830, 336885929, 330403749]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 295).prefactor = (2472521418539241/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 295).cutoff/(generalMeanRows 295).c)).2 =
    (1030340617313/2500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 295).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 295).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 295).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 295

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 295).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 295).criticalRate j.val*(generalMeanRows 295).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 295).c*(generalMeanRows 295).criticalPoint j.val)).2-
      (generalMeanRows 295).J/2-(generalMeanRows 295).error (generalMeanGrid j.val)+
      (generalMeanRows 295).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 295).c)).2-
      (generalMeanRows 295).J/2-(generalMeanRows 295).error 4 := by
  have he : (generalMeanRows 295).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 295) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 295)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0295

/-! Kernel-checked entropy margins for general spectral rectangle 296. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0296
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5458490010, 5278930833, 5107484093, 4943677079, 4787070868, 4637257372, 4493856705, 4356514829, 4224901432, 4098708024, 3977646214, 3861446152, 3749855116, 3642636230, 3539567291, 3440439704, 3345057505, 3253236471, 3164803298, 3079594849, 2997457465, 2918246325, 2841824859, 2768064206, 2696842713, 2628045471, 2561563883, 2497295267, 2435142488, 2375013611, 2316821581, 2260483930, 2205922497, 2153063168, 2101835640, 2052173193, 2004012479, 1957293332, 1911958576, 1867953861, 1825227498, 1783730310, 1743415491, 1704238473, 1666156804, 1629130030, 1593119585, 1558088689, 1524002255, 1490826791, 1458530322, 1427082306, 1396453560, 1366616185, 1337543505, 1309210002, 1281591252, 1254663874, 1228405478, 1202794609, 1177810707, 1153434055, 1129645746, 1106427636, 1083762308, 1061633039, 1040023767, 1018919055, 998304064, 978164525, 958486712, 939257414, 920463916, 902093971, 884135781, 866577977, 849409599, 832620078, 816199216, 800137175, 784424454, 769051881, 754010595, 739292034, 724887921, 710790252, 696991286, 683483535, 670259748, 657312907, 644636217, 632223092, 620067153, 608162215, 596502282, 585081539, 573894343, 562935220, 552198857, 541680093, 531373918, 521275465, 511380004, 501682938, 492179800, 482866243, 473738042, 464791087, 456021375, 447425015, 438998216, 430737288, 422638637, 414698763, 406914254, 399281788, 391798125, 384460107, 377264657, 370208771, 363289521]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 296).prefactor = (497886845382619/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 296).cutoff/(generalMeanRows 296).c)).2 =
    (210084209311233/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 296).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 296).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 296).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 296

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 296).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 296).criticalRate j.val*(generalMeanRows 296).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 296).c*(generalMeanRows 296).criticalPoint j.val)).2-
      (generalMeanRows 296).J/2-(generalMeanRows 296).error (generalMeanGrid j.val)+
      (generalMeanRows 296).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 296).c)).2-
      (generalMeanRows 296).J/2-(generalMeanRows 296).error 4 := by
  have he : (generalMeanRows 296).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 296) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 296)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0296

/-! Kernel-checked entropy margins for general spectral rectangle 297. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0297
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5176750275, 4987362966, 4806746194, 4634394504, 4469838181, 4312640126, 4162393086, 4018717161, 3881257573, 3749682656, 3623682042, 3502965020, 3387259045, 3276308390, 3169872910, 3067726922, 2969658175, 2875466910, 2784965001, 2697975158, 2614330202, 2533872392, 2456452804, 2381930763, 2310173312, 2241054724, 2174456044, 2110264674, 2048373977, 1988682919, 1931095727, 1875521572, 1821874285, 1770072072, 1720037269, 1671696094, 1624978434, 1579817627, 1536150274, 1493916052, 1453057546, 1413520086, 1375251598, 1338202460, 1302325375, 1267575239, 1233909030, 1201285694, 1169666043, 1139012656, 1109289789, 1080463287, 1052500505, 1025370225, 999042590, 973489034, 948682214, 924595952, 901205178, 878485874, 856415023, 834970558, 814131323, 793877022, 774188180, 755046106, 736432857, 718331197, 700724570, 683597068, 666933395, 650718850, 634939288, 619581104, 604631205, 590076987, 575906312, 562107494, 548669269, 535580787, 522831587, 510411583, 498311046, 486520594, 475031171, 463834038, 452920756, 442283177, 431913431, 421803914, 411947277, 402336417, 392964467, 383824784, 374910945, 366216734, 357736136, 349463329, 341392676, 333518719, 325836171, 318339910, 311024975, 303886555, 296919988, 290120755, 283484472, 277006889, 270683880, 264511444, 258485700, 252602876, 246859316, 241251466, 235775877, 230429198, 225208175, 220109645, 215130536, 210267861, 205518718]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 297).prefactor = (5272375110640663/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 297).cutoff/(generalMeanRows 297).c)).2 =
    (353640040243591/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 297).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 297).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 297).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 297

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 297).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 297).criticalRate j.val*(generalMeanRows 297).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 297).c*(generalMeanRows 297).criticalPoint j.val)).2-
      (generalMeanRows 297).J/2-(generalMeanRows 297).error (generalMeanGrid j.val)+
      (generalMeanRows 297).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 297).c)).2-
      (generalMeanRows 297).J/2-(generalMeanRows 297).error 4 := by
  have he : (generalMeanRows 297).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 297) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 297)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0297

/-! Kernel-checked entropy margins for general spectral rectangle 298. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0298
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5302873758, 5111462019, 4928878193, 4754613380, 4588194684, 4429182079, 4277165608, 4131762874, 3992616791, 3859393558, 3731780831, 3609486065, 3492235020, 3379770392, 3271850576, 3168248532, 3068750747, 2973156292, 2881275951, 2792931418, 2707954572, 2626186792, 2547478337, 2471687766, 2398681413, 2328332884, 2260522606, 2195137402, 2132070093, 2071219139, 2012488292, 1955786284, 1901026527, 1848126840, 1797009192, 1747599461, 1699827209, 1653625473, 1608930568, 1565681904, 1523821810, 1483295379, 1444050309, 1406036767, 1369207249, 1333516461, 1298921198, 1265380231, 1232854207, 1201305548, 1170698356, 1140998335, 1112172697, 1084190093, 1057020538, 1030635342, 1005007042, 980109346, 955917072, 932406093, 909553287, 887336487, 865734433, 844726735, 824293821, 804416909, 785077962, 766259655, 747945346, 730119037, 712765351, 695869498, 679417253, 663394928, 647789349, 632587831, 617778159, 603348564, 589287707, 575584660, 562228883, 549210215, 536518852, 524145334, 512080532, 500315631, 488842118, 477651771, 466736646, 456089066, 445701609, 435567099, 425678596, 416029386, 406612973, 397423070, 388453591, 379698642, 371152515, 362809683, 354664788, 346712639, 338948203, 331366601, 323963104, 316733120, 309672200, 302776024, 296040400, 289461259, 283034650, 276756739, 270623800, 264632215, 258778468, 253059143, 247470921, 242010574, 236674967, 231461048, 226365853]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 298).prefactor = (5310201629961279/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 298).cutoff/(generalMeanRows 298).c)).2 =
    (361483217704619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 298).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 298).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 298).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 298

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 298).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 298).criticalRate j.val*(generalMeanRows 298).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 298).c*(generalMeanRows 298).criticalPoint j.val)).2-
      (generalMeanRows 298).J/2-(generalMeanRows 298).error (generalMeanGrid j.val)+
      (generalMeanRows 298).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 298).c)).2-
      (generalMeanRows 298).J/2-(generalMeanRows 298).error 4 := by
  have he : (generalMeanRows 298).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 298) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 298)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0298

/-! Kernel-checked entropy margins for general spectral rectangle 299. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0299
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5593441419, 5412303368, 5239323480, 5074025803, 4915968427, 4764740522, 4619959678, 4481269529, 4348337622, 4220853489, 4098526920, 3981086383, 3868277608, 3759862288, 3655616901, 3555331636, 3458809406, 3365864953, 3276324017, 3190022581, 3106806175, 3026529229, 2949054486, 2874252449, 2802000882, 2732184340, 2664693731, 2599425923, 2536283363, 2475173733, 2416009633, 2358708273, 2303191198, 2249384029, 2197216220, 2146620826, 2097534301, 2049896292, 2003649459, 1958739301, 1915113992, 1872724233, 1831523108, 1791465950, 1752510218, 1714615379, 1677742796, 1641855628, 1606918732, 1572898568, 1539763120, 1507481807, 1476025416, 1445366020, 1415476921, 1386332579, 1357908557, 1330181460, 1303128885, 1276729372, 1250962351, 1225808104, 1201247719, 1177263050, 1153836680, 1130951887, 1108592607, 1086743407, 1065389449, 1044516466, 1024110733, 1004159044, 984648683, 965567407, 946903420, 928645354, 910782249, 893303538, 876199022, 859458862, 843073558, 827033935, 811331129, 795956575, 780901992, 766159372, 751720970, 737579288, 723727071, 710157293, 696863149, 683838045, 671075590, 658569589, 646314034, 634303097, 622531123, 610992622, 599682266, 588594879, 577725435, 567069048, 556620970, 546376587, 536331410, 526481074, 516821332, 507348052, 498057211, 488944893, 480007284, 471240671, 462641434, 454206048, 445931077, 437813171, 429849064, 422035572, 414369587, 406848080, 399468093]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 299).prefactor = (5012925448215309/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 299).cutoff/(generalMeanRows 299).c)).2 =
    (107066407213771/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 299).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 299).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 299).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 299

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 299).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 299).criticalRate j.val*(generalMeanRows 299).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 299).c*(generalMeanRows 299).criticalPoint j.val)).2-
      (generalMeanRows 299).J/2-(generalMeanRows 299).error (generalMeanGrid j.val)+
      (generalMeanRows 299).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 299).c)).2-
      (generalMeanRows 299).J/2-(generalMeanRows 299).error 4 := by
  have he : (generalMeanRows 299).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 299) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 299)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0299

/-! Kernel-checked entropy margins for general spectral rectangle 300. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0300
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5732276970, 5549591870, 5375110502, 5208353609, 5048876246, 4896264788, 4750134254, 4610125910, 4475905119, 4347159403, 4223596696, 4104943756, 3990944735, 3881359871, 3775964298, 3674546968, 3576909653, 3482866039, 3392240898, 3304869318, 3220596004, 3139274627, 3060767232, 2984943681, 2911681147, 2840863640, 2772381574, 2706131357, 2642015018, 2579939858, 2519818125, 2461566710, 2405106867, 2350363950, 2297267172, 2245749370, 2195746799, 2147198926, 2100048250, 2054240124, 2009722593, 1966446239, 1924364044, 1883431248, 1843605229, 1804845382, 1767113007, 1730371211, 1694584803, 1659720203, 1625745362, 1592629672, 1560343895, 1528860090, 1498151543, 1468192705, 1438959132, 1410427427, 1382575186, 1355380949, 1328824153, 1302885084, 1277544836, 1252785274, 1228588989, 1204939269, 1181820064, 1159215950, 1137112102, 1115494267, 1094348731, 1073662300, 1053422273, 1033616417, 1014232949, 995260512, 976688158, 958505329, 940701839, 923267856, 906193889, 889470772, 873089648, 857041958, 841319428, 825914053, 810818092, 796024052, 781524679, 767312948, 753382054, 739725403, 726336603, 713209457, 700337953, 687716258, 675338713, 663199821, 651294249, 639616811, 628162473, 616926339, 605903653, 595089787, 584480241, 574070638, 563856716, 553834329, 543999439, 534348114, 524876523, 515580936, 506457716, 497503318, 488714287, 480087253, 471618930, 463306111, 455145669, 447134550, 439269776]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 300).prefactor = (5047215402940221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 300).cutoff/(generalMeanRows 300).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 300).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 300).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 300).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 300

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 300).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 300).criticalRate j.val*(generalMeanRows 300).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 300).c*(generalMeanRows 300).criticalPoint j.val)).2-
      (generalMeanRows 300).J/2-(generalMeanRows 300).error (generalMeanGrid j.val)+
      (generalMeanRows 300).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 300).c)).2-
      (generalMeanRows 300).J/2-(generalMeanRows 300).error 4 := by
  have he : (generalMeanRows 300).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 300) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 300)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0300

/-! Kernel-checked entropy margins for general spectral rectangle 301. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0301
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5049621314, 4870956045, 4700478420, 4537715635, 4382228427, 4233608151, 4091474171, 3955471520, 3825268802, 3700556304, 3581044290, 3466461458, 3356553540, 3251082032, 3149823035, 3052566198, 2959113753, 2869279630, 2782888648, 2699775770, 2619785415, 2542770832, 2468593513, 2397122659, 2328234683, 2261812750, 2197746348, 2135930898, 2076267382, 2018662008, 1963025885, 1909274736, 1857328618, 1807111666, 1758551854, 1711580775, 1666133427, 1622148021, 1579565797, 1538330855, 1498389991, 1459692554, 1422190296, 1385837248, 1350589592, 1316405545, 1283245249, 1251070674, 1219845511, 1189535090, 1160106290, 1131527461, 1103768345, 1076800007, 1050594766, 1025126132, 1000368747, 976298326, 952891607, 930126295, 907981022, 886435295, 865469457, 845064645, 825202754, 805866399, 787038882, 768704160, 750846811, 733452012, 716505503, 699993569, 683903011, 668221120, 652935663, 638034854, 623507338, 609342171, 595528803, 582057059, 568917124, 556099529, 543595133, 531395111, 519490940, 507874390, 496537504, 485472596, 474672232, 464129226, 453836625, 443787704, 433975953, 424395072, 415038960, 405901709, 396977595, 388261074, 379746772, 371429479, 363304144, 355365870, 347609905, 340031640, 332626601, 325390447, 318318964, 311408058, 304653756, 298052198, 291599632, 285292414, 279127003, 273099954, 267207922, 261447650, 255815974, 250309815, 244926176, 239662144, 234514881]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 301).prefactor = (2492423833136257/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 301).cutoff/(generalMeanRows 301).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 301).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 301).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 301).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 301

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 301).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 301).criticalRate j.val*(generalMeanRows 301).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 301).c*(generalMeanRows 301).criticalPoint j.val)).2-
      (generalMeanRows 301).J/2-(generalMeanRows 301).error (generalMeanGrid j.val)+
      (generalMeanRows 301).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 301).c)).2-
      (generalMeanRows 301).J/2-(generalMeanRows 301).error 4 := by
  have he : (generalMeanRows 301).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 301) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 301)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0301

/-! Kernel-checked entropy margins for general spectral rectangle 302. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0302
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5172050294, 4991594452, 4819375981, 4654918938, 4497781177, 4347551398, 4203846517, 4066309310, 3934606302, 3808425857, 3687476464, 3571485180, 3460196218, 3353369672, 3250780342, 3152216674, 3057479787, 2966382578, 2878748911, 2794412859, 2713218023, 2635016886, 2559670235, 2487046614, 2417021828, 2349478474, 2284305519, 2221397894, 2160656131, 2101986013, 2045298262, 1990508236, 1937535653, 1886304335, 1836741963, 1788779856, 1742352758, 1697398644, 1653858533, 1611676318, 1570798604, 1531174556, 1492755760, 1455496088, 1419351573, 1384280294, 1350242262, 1317199321, 1285115048, 1253954662, 1223684939, 1194274128, 1165691878, 1137909165, 1110898222, 1084632478, 1059086497, 1034235918, 1010057408, 986528601, 963628063, 941335233, 919630393, 898494617, 877909739, 857858316, 838323592, 819289465, 800740459, 782661695, 765038859, 747858180, 731106407, 714770779, 698839007, 683299255, 668140116, 653350592, 638920082, 624838360, 611095558, 597682155, 584588958, 571807091, 559327980, 547143341, 535245166, 523625717, 512277507, 501193298, 490366085, 479789090, 469455750, 459359712, 449494823, 439855121, 430434831, 421228353, 412230261, 403435291, 394838340, 386434455, 378218832, 370186807, 362333855, 354655579, 347147711, 339806106, 332626734, 325605682, 318739145, 312023426, 305454928, 299030155, 292745707, 286598275, 280584639, 274701669, 268946316, 263315611, 257806666]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 302).prefactor = (2509748702951903/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 302).cutoff/(generalMeanRows 302).c)).2 =
    (15296547849907/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 302).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 302).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 302).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 302

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 302).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 302).criticalRate j.val*(generalMeanRows 302).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 302).c*(generalMeanRows 302).criticalPoint j.val)).2-
      (generalMeanRows 302).J/2-(generalMeanRows 302).error (generalMeanGrid j.val)+
      (generalMeanRows 302).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 302).c)).2-
      (generalMeanRows 302).J/2-(generalMeanRows 302).error 4 := by
  have he : (generalMeanRows 302).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 302) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 302)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0302

/-! Kernel-checked entropy margins for general spectral rectangle 303. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0303
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4878708219, 4699189420, 4527967028, 4364564650, 4208539511, 4059479524, 3917000675, 3780744687, 3650376919, 3525584475, 3406074499, 3291572632, 3181821610, 3076579996, 2975621020, 2878731522, 2785710987, 2696370661, 2610532741, 2528029628, 2448703243, 2372404399, 2298992211, 2228333568, 2160302628, 2094780362, 2031654127, 1970817269, 1912168755, 1855612834, 1801058717, 1748420282, 1697615799, 1648567668, 1601202188, 1555449322, 1511242496, 1468518397, 1427216796, 1387280367, 1348654533, 1311287315, 1275129183, 1240132934, 1206253557, 1173448120, 1141675661, 1110897081, 1081075049, 1052173908, 1024159590, 996999533, 970662604, 945119030, 920340322, 896299221, 872969627, 850326547, 828346041, 807005166, 786281933, 766155257, 746604916, 727611509, 709156416, 691221763, 673790387, 656845802, 640372167, 624354258, 608777439, 593627637, 578891312, 564555439, 550607480, 537035368, 523827478, 510972618, 498459999, 486279229, 474420287, 462873511, 451629583, 440679513, 430014627, 419626552, 409507205, 399648780, 390043739, 380684798, 371564918, 362677296, 354015356, 345572737, 337343288, 329321059, 321500291, 313875412, 306441028, 299191915, 292123015, 285229430, 278506412, 271949364, 265553828, 259315483, 253230142, 247293741, 241502343, 235852125, 230339381, 224960514, 219712032, 214590546, 209592766, 204715499, 199955643, 195310183, 190776194, 186350832, 182031335]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 303).prefactor = (5026062098367719/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 303).cutoff/(generalMeanRows 303).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 303).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 303).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 303).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 303

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 303).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 303).criticalRate j.val*(generalMeanRows 303).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 303).c*(generalMeanRows 303).criticalPoint j.val)).2-
      (generalMeanRows 303).J/2-(generalMeanRows 303).error (generalMeanGrid j.val)+
      (generalMeanRows 303).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 303).c)).2-
      (generalMeanRows 303).J/2-(generalMeanRows 303).error 4 := by
  have he : (generalMeanRows 303).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 303) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 303)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0303

/-! Kernel-checked entropy margins for general spectral rectangle 304. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0304
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4995609714, 4814170599, 4641081156, 4475861862, 4318067053, 4167281982, 4023120182, 3885221110, 3753248028, 3626886105, 3505840688, 3389835757, 3278612508, 3171928072, 3069554353, 2971276959, 2876894227, 2786216340, 2699064502, 2615270190, 2534674467, 2457127343, 2382487186, 2310620187, 2241399854, 2174706548, 2110427056, 2048454194, 1988686429, 1931027544, 1875386313, 1821676202, 1769815096, 1719725033, 1671331970, 1624565550, 1579358897, 1535648413, 1493373596, 1452476869, 1412903413, 1374601019, 1337519942, 1301612771, 1266834299, 1233141408, 1200492957, 1168849678, 1138174075, 1108430335, 1079584240, 1051603084, 1024455595, 998111864, 972543277, 947722445, 923623149, 900220278, 877489775, 855408589, 833954621, 813106680, 792844439, 773148397, 753999834, 735380778, 717273972, 699662833, 682531428, 665864443, 649647152, 633865390, 618505532, 603554465, 588999567, 574828682, 561030104, 547592555, 534505167, 521757462, 509339339, 497241056, 485453213, 473966742, 462772888, 451863200, 441229517, 430863955, 420758899, 410906986, 401301104, 391934371, 382800137, 373891965, 365203629, 356729105, 348462559, 340398347, 332531000, 324855222, 317365883, 310058011, 302926790, 295967548, 289175758, 282547028, 276077102, 269761846, 263597253, 257579433, 251704610, 245969120, 240369404, 234902006, 229563570, 224350836, 219260637, 214289894, 209435616, 204694896, 200064908]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 304).prefactor = (5061569805991533/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 304).cutoff/(generalMeanRows 304).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 304).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 304).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 304).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 304

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 304).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 304).criticalRate j.val*(generalMeanRows 304).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 304).c*(generalMeanRows 304).criticalPoint j.val)).2-
      (generalMeanRows 304).J/2-(generalMeanRows 304).error (generalMeanGrid j.val)+
      (generalMeanRows 304).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 304).c)).2-
      (generalMeanRows 304).J/2-(generalMeanRows 304).error 4 := by
  have he : (generalMeanRows 304).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 304) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 304)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0304

/-! Kernel-checked entropy margins for general spectral rectangle 305. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0305
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5390005209, 5207296541, 5032866332, 4866235552, 4706959244, 4554623552, 4408843065, 4269258447, 4135534296, 4007357230, 3884434148, 3766490666, 3653269690, 3544530127, 3440045705, 3339603900, 3243004956, 3150060982, 3060595130, 2974440840, 2891441140, 2811448006, 2734321772, 2659930582, 2588149884, 2518861966, 2451955521, 2387325244, 2324871462, 2264499787, 2206120791, 2149649709, 2095006161, 2042113886, 1990900504, 1941297288, 1893238952, 1846663451, 1801511797, 1757727888, 1715258342, 1674052345, 1634061511, 1595239746, 1557543121, 1520929759, 1485359718, 1450794893, 1417198912, 1384537048, 1352776133, 1321884472, 1291831769, 1262589058, 1234128626, 1206423958, 1179449670, 1153181457, 1127596033, 1102671084, 1078385221, 1054717931, 1031649535, 1009161150, 987234648, 965852620, 944998342, 924655743, 904809374, 885444379, 866546466, 848101884, 830097393, 812520248, 795358169, 778599325, 762232314, 746246139, 730630196, 715374254, 700468439, 685903219, 671669387, 657758052, 644160620, 630868788, 617874524, 605170064, 592747893, 580600742, 568721573, 557103573, 545740142, 534624888, 523751615, 513114320, 502707180, 492524550, 482560954, 472811078, 463269766, 453932012, 444792956, 435847877, 427092192, 418521444, 410131304, 401917564, 393876132, 386003030, 378294387, 370746439, 363355523, 356118072, 349030618, 342089780, 335292271, 328634884, 322114501, 315728078, 309472655]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 305).prefactor = (315899249769793/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 305).cutoff/(generalMeanRows 305).c)).2 =
    (398162053215813/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 305).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 305).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 305).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 305

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 305).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 305).criticalRate j.val*(generalMeanRows 305).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 305).c*(generalMeanRows 305).criticalPoint j.val)).2-
      (generalMeanRows 305).J/2-(generalMeanRows 305).error (generalMeanGrid j.val)+
      (generalMeanRows 305).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 305).c)).2-
      (generalMeanRows 305).J/2-(generalMeanRows 305).error 4 := by
  have he : (generalMeanRows 305).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 305) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 305)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0305

/-! Kernel-checked entropy margins for general spectral rectangle 306. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0306
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5522297726, 5337873823, 5161776987, 4993524924, 4832669673, 4678794616, 4531511799, 4390459538, 4255300270, 4125718618, 4001419638, 3882127247, 3767582781, 3657543695, 3551782377, 3450085065, 3352250856, 3258090801, 3167427075, 3080092212, 2995928405, 2914786857, 2836527188, 2761016882, 2688130777, 2617750599, 2549764521, 2484066757, 2420557191, 2359141026, 2299728458, 2242234374, 2186578071, 2132682994, 2080476492, 2029889586, 1980856759, 1933315753, 1887207386, 1842475375, 1799066173, 1756928814, 1716014773, 1676277826, 1637673929, 1600161093, 1563699280, 1528250290, 1493777670, 1460246614, 1427623883, 1395877716, 1364977758, 1334894985, 1305601634, 1277071143, 1249278083, 1222198106, 1195807889, 1170085083, 1145008264, 1120556886, 1096711243, 1073452421, 1050762264, 1028623338, 1007018895, 985932837, 965349693, 945254582, 925633190, 906471743, 887756979, 869476129, 851616893, 834167417, 817116273, 800452446, 784165307, 768244601, 752680430, 737463239, 722583796, 708033186, 693802790, 679884277, 666269592, 652950940, 639920782, 627171821, 614696989, 602489445, 590542560, 578849911, 567405273, 556202609, 545236069, 534499972, 523988812, 513697240, 503620068, 493752256, 484088908, 474625270, 465356721, 456278771, 447387054, 438677325, 430145456, 421787430, 413599339, 405577381, 397717855, 390017156, 382471775, 375078294, 367833385, 360733803, 353776387, 346958057, 340275809]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 306).prefactor = (5089521111668017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 306).cutoff/(generalMeanRows 306).c)).2 =
    (406130222864989/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 306).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 306).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 306).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 306

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 306).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 306).criticalRate j.val*(generalMeanRows 306).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 306).c*(generalMeanRows 306).criticalPoint j.val)).2-
      (generalMeanRows 306).J/2-(generalMeanRows 306).error (generalMeanGrid j.val)+
      (generalMeanRows 306).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 306).c)).2-
      (generalMeanRows 306).J/2-(generalMeanRows 306).error 4 := by
  have he : (generalMeanRows 306).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 306) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 306)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0306

/-! Kernel-checked entropy margins for general spectral rectangle 307. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0307
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5115817784, 4932470021, 4757524888, 4590499684, 4430945823, 4278445862, 4132610848, 3993077944, 3859508294, 3731585103, 3609011908, 3491511008, 3378822043, 3270700703, 3166917552, 3067256957, 2971516103, 2879504100, 2791041157, 2705957826, 2624094307, 2545299808, 2469431952, 2396356233, 2325945509, 2258079538, 2192644543, 2129532809, 2068642316, 2009876383, 1953143353, 1898356292, 1845432705, 1794294278, 1744866635, 1697079109, 1650864528, 1606159022, 1562901829, 1521035127, 1480503866, 1441255621, 1403240440, 1366410716, 1330721060, 1296128176, 1262590758, 1230069377, 1198526387, 1167925830, 1138233350, 1109416106, 1081442700, 1054283102, 1027908577, 1002291625, 977405914, 953226228, 929728408, 906889301, 884686709, 863099347, 842106797, 821689464, 801828541, 782505969, 763704403, 745407178, 727598278, 710262307, 693384457, 676950487, 660946691, 645359879, 630177350, 615386875, 600976671, 586935386, 573252075, 559916189, 546917552, 534246349, 521893108, 509848688, 498104262, 486651310, 475481596, 464587168, 453960339, 443593676, 433479996, 423612348, 413984012, 404588483, 395419464, 386470863, 377736778, 369211496, 360889479, 352765365, 344833956, 337090212, 329529249, 322146331, 314936862, 307896386, 301020578, 294305241, 287746302, 281339806, 275081913, 268968893, 262997124, 257163087, 251463362, 245894625, 240453647, 235137288, 229942494, 224866296, 219905808]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 307).prefactor = (5097328365530033/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 307).cutoff/(generalMeanRows 307).c)).2 =
    (90234835681301/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 307).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 307).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 307).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 307

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 307).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 307).criticalRate j.val*(generalMeanRows 307).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 307).c*(generalMeanRows 307).criticalPoint j.val)).2-
      (generalMeanRows 307).J/2-(generalMeanRows 307).error (generalMeanGrid j.val)+
      (generalMeanRows 307).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 307).c)).2-
      (generalMeanRows 307).J/2-(generalMeanRows 307).error 4 := by
  have he : (generalMeanRows 307).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 307) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 307)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0307

/-! Kernel-checked entropy margins for general spectral rectangle 308. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0308
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5328919137, 5143110603, 4965750045, 4796351701, 4634464200, 4479667566, 4331570536, 4189808170, 4054039697, 3923946579, 3799230765, 3679613107, 3564831932, 3454641735, 3348811993, 3247126087, 3149380307, 3055382953, 2964953499, 2877921834, 2794127558, 2713419338, 2635654311, 2560697533, 2488421471, 2418705530, 2351435621, 2286503751, 2223807648, 2163250414, 2104740199, 2048189897, 1993516864, 1940642656, 1889492785, 1839996487, 1792086506, 1745698902, 1700772853, 1657250487, 1615076715, 1574199075, 1534567593, 1496134639, 1458854808, 1422684793, 1387583280, 1353510834, 1320429808, 1288304242, 1257099779, 1226783582, 1197324254, 1168691765, 1140857384, 1113793609, 1087474113, 1061873675, 1036968136, 1012734339, 989150083, 966194074, 943845887, 922085916, 900895342, 880256092, 860150803, 840562791, 821476021, 802875071, 784745109, 767071863, 749841599, 733041092, 716657608, 700678879, 685093082, 669888823, 655055113, 640581355, 626457325, 612673157, 599219327, 586086637, 573266205, 560749449, 548528075, 536594066, 524939671, 513557393, 502439978, 491580409, 480971891, 470607847, 460481909, 450587908, 440919865, 431471988, 422238663, 413214445, 404394056, 395772373, 387344430, 379105404, 371050617, 363175526, 355475718, 347946911, 340584943, 333385770, 326345462, 319460202, 312726275, 306140074, 299698086, 293396897, 287233187, 281203722, 275305359, 269535035, 263889773]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 308).prefactor = (5133339549181071/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 308).cutoff/(generalMeanRows 308).c)).2 =
    (37644352926117/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 308).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 308).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 308).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 308

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 308).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 308).criticalRate j.val*(generalMeanRows 308).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 308).c*(generalMeanRows 308).criticalPoint j.val)).2-
      (generalMeanRows 308).J/2-(generalMeanRows 308).error (generalMeanGrid j.val)+
      (generalMeanRows 308).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 308).c)).2-
      (generalMeanRows 308).J/2-(generalMeanRows 308).error 4 := by
  have he : (generalMeanRows 308).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 308) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 308)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0308

/-! Kernel-checked entropy margins for general spectral rectangle 309. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0309
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5810966264, 5625773372, 5448896827, 5279850794, 5118184220, 4963477803, 4815341275, 4673410980, 4537347686, 4406834626, 4281575723, 4161293986, 4045730054, 3934640874, 3827798494, 3724988967, 3626011344, 3530676755, 3438807566, 3350236601, 3264806433, 3182368725, 3102783627, 3025919216, 2951650977, 2879861329, 2810439182, 2743279521, 2678283031, 2615355740, 2554408692, 2495357636, 2438122745, 2382628351, 2328802691, 2276577684, 2225888706, 2176674397, 2128876465, 2082439512, 2037310871, 1993440445, 1950780571, 1909285874, 1868913147, 1829621227, 1791370885, 1754124720, 1717847056, 1682503856, 1648062629, 1614492346, 1581763369, 1549847373, 1518717277, 1488347183, 1458712309, 1429788937, 1401554357, 1373986814, 1347065462, 1320770317, 1295082213, 1269982766, 1245454329, 1221479960, 1198043388, 1175128978, 1152721702, 1130807110, 1109371300, 1088400899, 1067883028, 1047805289, 1028155736, 1008922857, 990095553, 971663121, 953615235, 935941929, 918633581, 901680899, 885074904, 868806921, 852868561, 837251711, 821948521, 806951397, 792252985, 777846164, 763724035, 749879914, 736307321, 722999973, 709951776, 697156818, 684609361, 672303835, 660234829, 648397091, 636785514, 625395138, 614221138, 603258826, 592503639, 581951138, 571597006, 561437038, 551467140, 541683327, 532081716, 522658525, 513410067, 504332748, 495423067, 486677606, 478093035, 469666102, 461393638, 453272548, 445299810]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 309).prefactor = (5116500578379481/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 309).cutoff/(generalMeanRows 309).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 309).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 309).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 309).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 309

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 309).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 309).criticalRate j.val*(generalMeanRows 309).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 309).c*(generalMeanRows 309).criticalPoint j.val)).2-
      (generalMeanRows 309).J/2-(generalMeanRows 309).error (generalMeanGrid j.val)+
      (generalMeanRows 309).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 309).c)).2-
      (generalMeanRows 309).J/2-(generalMeanRows 309).error 4 := by
  have he : (generalMeanRows 309).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 309) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 309)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0309

/-! Kernel-checked entropy margins for general spectral rectangle 310. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0310
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5647408067, 5446531584, 5254843833, 5071817479, 4896962427, 4729822568, 4569972886, 4417016867, 4270584171, 4130328537, 3995925895, 3867072655, 3743484160, 3624893274, 3511049103, 3401715821, 3296671605, 3195707656, 3098627296, 3005245151, 2915386384, 2828886005, 2745588220, 2665345835, 2588019713, 2513478255, 2441596935, 2372257857, 2305349348, 2240765586, 2178406238, 2118176140, 2059984988, 2003747054, 1949380919, 1896809225, 1845958444, 1796758657, 1749143355, 1703049247, 1658416077, 1615186465, 1573305742, 1532721807, 1493384988, 1455247910, 1418265375, 1382394244, 1347593331, 1313823302, 1281046575, 1249227235, 1218330943, 1188324860, 1159177569, 1130859004, 1103340383, 1076594144, 1050593883, 1025314299, 1000731141, 976821156, 953562038, 930932388, 908911668, 887480160, 866618927, 846309777, 826535232, 807278487, 788523387, 770254393, 752456555, 735115485, 718217333, 701748762, 685696927, 670049450, 654794403, 639920286, 625416010, 611270879, 597474573, 584017133, 570888944, 558080723, 545583501, 533388617, 521487699, 509872653, 498535657, 487469145, 476665796, 466118528, 455820489, 445765044, 435945768, 426356440, 416991033, 407843708, 398908805, 390180839, 381654492, 373324606, 365186177, 357234354, 349464425, 341871821, 334452105, 327200968, 320114227, 313187820, 306417798, 299800328, 293331681, 287008234, 280826468, 274782957, 268874372, 263097474, 257449113]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 310).prefactor = (1103169000447277/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 310).cutoff/(generalMeanRows 310).c)).2 =
    (363346082755771/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 310).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 310).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 310).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 310

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 310).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 310).criticalRate j.val*(generalMeanRows 310).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 310).c*(generalMeanRows 310).criticalPoint j.val)).2-
      (generalMeanRows 310).J/2-(generalMeanRows 310).error (generalMeanGrid j.val)+
      (generalMeanRows 310).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 310).c)).2-
      (generalMeanRows 310).J/2-(generalMeanRows 310).error 4 := by
  have he : (generalMeanRows 310).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 310) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 310)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0310

/-! Kernel-checked entropy margins for general spectral rectangle 311. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0311
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5758357757, 5571881357, 5393770481, 5223539512, 5060737464, 4904944967, 4755771557, 4612853272, 4475850472, 4344445894, 4218342880, 4097263791, 3980948553, 3869153345, 3761649400, 3658221914, 3558669045, 3462801003, 3370439205, 3281415512, 3195571514, 3112757881, 3032833762, 2955666226, 2881129753, 2809105754, 2739482133, 2672152878, 2607017682, 2543981589, 2482954671, 2423851716, 2366591950, 2311098771, 2257299497, 2205125144, 2154510202, 2105392440, 2057712714, 2011414792, 1966445190, 1922753014, 1880289819, 1839009472, 1798868021, 1759823582, 1721836220, 1684867846, 1648882119, 1613844350, 1579721416, 1546481676, 1514094896, 1482532171, 1451765860, 1421769519, 1392517840, 1363986592, 1336152570, 1308993539, 1282488188, 1256616084, 1231357627, 1206694011, 1182607184, 1159079811, 1136095241, 1113637474, 1091691127, 1070241410, 1049274093, 1028775482, 1008732396, 989132141, 969962485, 951211645, 932868258, 914921367, 897360403, 880175165, 863355807, 846892818, 830777014, 814999517, 799551748, 784425409, 769612475, 755105182, 740896013, 726977693, 713343173, 699985628, 686898440, 674075198, 661509683, 649195864, 637127889, 625300080, 613706924, 602343070, 591203318, 580282619, 569576065, 559078885, 548786441, 538694224, 528797846, 519093039, 509575647, 500241629, 491087047, 482108067, 473300955, 464662074, 456187877, 447874910, 439719804, 431719276, 423870124, 416169222, 408613524]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 311).prefactor = (2562449218875857/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 311).cutoff/(generalMeanRows 311).c)).2 =
    (211129802397437/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 311).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 311).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 311).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 311

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 311).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 311).criticalRate j.val*(generalMeanRows 311).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 311).c*(generalMeanRows 311).criticalPoint j.val)).2-
      (generalMeanRows 311).J/2-(generalMeanRows 311).error (generalMeanGrid j.val)+
      (generalMeanRows 311).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 311).c)).2-
      (generalMeanRows 311).J/2-(generalMeanRows 311).error 4 := by
  have he : (generalMeanRows 311).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 311) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 311)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0311

/-! Kernel-checked entropy margins for general spectral rectangle 312. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0312
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5064346758, 4892852933, 4729179293, 4572868086, 4423494398, 4280663287, 4144007220, 4013183781, 3887873603, 3767778517, 3652619876, 3542137030, 3436085959, 3334238016, 3236378788, 3142307058, 3051833856, 2964781587, 2880983232, 2800281621, 2722528752, 2647585179, 2575319433, 2505607499, 2438332328, 2373383381, 2310656219, 2250052108, 2191477665, 2134844524, 2080069021, 2027071912, 1975778100, 1926116387, 1878019240, 1831422574, 1786265547, 1742490373, 1700042144, 1658868664, 1618920291, 1580149797, 1542512229, 1505964782, 1470466677, 1435979055, 1402464865, 1369888770, 1338217052, 1307417525, 1277459452, 1248313473, 1219951526, 1192346781, 1165473579, 1139307365, 1113824639, 1089002895, 1064820575, 1041257019, 1018292421, 995907786, 974084890, 952806242, 932055050, 911815182, 892071141, 872808030, 854011524, 835667846, 817763738, 800286436, 783223653, 766563551, 750294723, 734406173, 718887300, 703727877, 688918035, 674448249, 660309322, 646492372, 632988816, 619790359, 606888982, 594276930, 581946701, 569891035, 558102905, 546575509, 535302256, 524276764, 513492847, 502944507, 492625933, 482531485, 472655695, 462993254, 453539013, 444287970, 435235269, 426376196, 417706167, 409220730, 400915559, 392786446, 384829301, 377040147, 369415113, 361950434, 354642446, 347487583, 340482375, 333623439, 326907484, 320331305, 313891776, 307585855, 301410576, 295363047, 289440451]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 312).prefactor = (2431632069524463/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 312).cutoff/(generalMeanRows 312).c)).2 =
    (206661346723247/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 312).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 312).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 312).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 312

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 312).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 312).criticalRate j.val*(generalMeanRows 312).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 312).c*(generalMeanRows 312).criticalPoint j.val)).2-
      (generalMeanRows 312).J/2-(generalMeanRows 312).error (generalMeanGrid j.val)+
      (generalMeanRows 312).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 312).c)).2-
      (generalMeanRows 312).J/2-(generalMeanRows 312).error 4 := by
  have he : (generalMeanRows 312).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 312) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 312)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0312

/-! Kernel-checked entropy margins for general spectral rectangle 313. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0313
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5458757422, 5271101860, 5091946005, 4920800798, 4757211838, 4600756354, 4451040511, 4307696994, 4170382840, 4038777489, 3912581017, 3791512549, 3675308811, 3563722817, 3456522675, 3353490496, 3254421396, 3159122582, 3067412522, 2979120167, 2894084251, 2812152635, 2733181710, 2657035840, 2583586849, 2512713548, 2444301291, 2378241574, 2314431649, 2252774175, 2193176890, 2135552307, 2079817427, 2025893478, 1973705664, 1923182935, 1874257774, 1826865991, 1780946537, 1736441326, 1693295068, 1651455118, 1610871326, 1571495903, 1533283291, 1496190042, 1460174709, 1425197734, 1391221352, 1358209493, 1326127699, 1294943033, 1264624007, 1235140503, 1206463708, 1178566042, 1151421100, 1125003594, 1099289292, 1074254974, 1049878374, 1026138139, 1003013782, 980485643, 958534845, 937143262, 916293477, 895968757, 876153012, 856830772, 837987156, 819607844, 801679052, 784187509, 767120433, 750465508, 734210866, 718345064, 702857069, 687736236, 672972295, 658555333, 644475779, 630724389, 617292234, 604170685, 591351401, 578826319, 566587639, 554627816, 542939549, 531515773, 520349645, 509434540, 498764040, 488331928, 478132176, 468158943, 458406565, 448869548, 439542564, 430420440, 421498160, 412770852, 404233785, 395882367, 387712136, 379718756, 371898016, 364245821, 356758192, 349431257, 342261254, 335244521, 328377496, 321656716, 315078806, 308640483, 302338553, 296169902, 290131500]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 313).prefactor = (646200642707821/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 313).cutoff/(generalMeanRows 313).c)).2 =
    (96071676680549/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 313).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 313).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 313).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 313

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 313).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 313).criticalRate j.val*(generalMeanRows 313).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 313).c*(generalMeanRows 313).criticalPoint j.val)).2-
      (generalMeanRows 313).J/2-(generalMeanRows 313).error (generalMeanGrid j.val)+
      (generalMeanRows 313).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 313).c)).2-
      (generalMeanRows 313).J/2-(generalMeanRows 313).error 4 := by
  have he : (generalMeanRows 313).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 313) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 313)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0313

/-! Kernel-checked entropy margins for general spectral rectangle 314. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0314
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5689486783, 5499544717, 5318144732, 5144794500, 4979036638, 4820445664, 4668625274, 4523205903, 4383842543, 4250212768, 4122014963, 3998966713, 3880803346, 3767276609, 3658153460, 3553214970, 3452255316, 3355080860, 3261509303, 3171368913, 3084497809, 3000743305, 2919961301, 2842015728, 2766778028, 2694126672, 2623946724, 2556129419, 2490571791, 2427176309, 2365850553, 2306506904, 2249062254, 2193437746, 2139558518, 2087353473, 2036755062, 1987699077, 1940124467, 1893973152, 1849189864, 1805721982, 1763519393, 1722534350, 1682721344, 1644036982, 1606439874, 1569890524, 1534351233, 1499785998, 1466160428, 1433441660, 1401598274, 1370600225, 1340418771, 1311026402, 1282396785, 1254504699, 1227325982, 1200837477, 1175016985, 1149843215, 1125295740, 1101354957, 1078002045, 1055218929, 1032988246, 1011293307, 990118067, 969447099, 949265560, 929559164, 910314162, 891517311, 873155856, 855217504, 837690408, 820563142, 803824687, 787464411, 771472051, 755837699, 740551787, 725605071, 710988619, 696693795, 682712251, 669035911, 655656962, 642567841, 629761231, 617230041, 604967408, 592966679, 581221409, 569725347, 558472435, 547456796, 536672728, 526114700, 515777340, 505655436, 495743925, 486037888, 476532549, 467223264, 458105519, 449174929, 440427225, 431858259, 423463993, 415240499, 407183954, 399290638, 391556926, 383979291, 376554296, 369278595, 362148925, 355162108, 348315046]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 314).prefactor = (5206126940300977/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 314).cutoff/(generalMeanRows 314).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 314).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 314).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 314).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 314

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 314).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 314).criticalRate j.val*(generalMeanRows 314).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 314).c*(generalMeanRows 314).criticalPoint j.val)).2-
      (generalMeanRows 314).J/2-(generalMeanRows 314).error (generalMeanGrid j.val)+
      (generalMeanRows 314).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 314).c)).2-
      (generalMeanRows 314).J/2-(generalMeanRows 314).error 4 := by
  have he : (generalMeanRows 314).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 314) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 314)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0314

/-! Kernel-checked entropy margins for general spectral rectangle 315. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0315
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5770159978, 5577524657, 5393552540, 5217744314, 5049636115, 4888796425, 4734823321, 4587341999, 4446002557, 4310478000, 4180462434, 4055669440, 3935830594, 3820694122, 3710023679, 3603597230, 3501206034, 3402653708, 3307755367, 3216336846, 3128233967, 3043291878, 2961364439, 2882313649, 2806009127, 2732327623, 2661152569, 2592373659, 2525886467, 2461592078, 2399396764, 2339211660, 2280952483, 2224539256, 2169896056, 2116950778, 2065634914, 2015883348, 1967634161, 1920828451, 1875410164, 1831325936, 1788524942, 1746958758, 1706581230, 1667348349, 1629218138, 1592150543, 1556107328, 1521051980, 1486949622, 1453766923, 1421472019, 1390034438, 1359425030, 1329615897, 1300580331, 1272292753, 1244728660, 1217864566, 1191677956, 1166147239, 1141251696, 1116971448, 1093287407, 1070181242, 1047635343, 1025632783, 1004157293, 983193224, 962725523, 942739704, 923221820, 904158442, 885536633, 867343928, 849568309, 832198190, 815222395, 798630140, 782411019, 766554982, 751052326, 735893676, 721069972, 706572457, 692392664, 678522402, 664953748, 651679032, 638690832, 625981959, 613545450, 601374558, 589462747, 577803679, 566391208, 555219374, 544282396, 533574661, 523090725, 512825299, 502773249, 492929587, 483289468, 473848183, 464601155, 455543935, 446672194, 437981726, 429468434, 421128337, 412957556, 404952317, 397108946, 389423866, 381893589, 374514723, 367283959, 360198074, 353253925]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 315).prefactor = (2639973204466037/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 315).cutoff/(generalMeanRows 315).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 315).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 315).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 315).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 315

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 315).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 315).criticalRate j.val*(generalMeanRows 315).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 315).c*(generalMeanRows 315).criticalPoint j.val)).2-
      (generalMeanRows 315).J/2-(generalMeanRows 315).error (generalMeanGrid j.val)+
      (generalMeanRows 315).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 315).c)).2-
      (generalMeanRows 315).J/2-(generalMeanRows 315).error 4 := by
  have he : (generalMeanRows 315).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 315) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 315)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0315

/-! Kernel-checked entropy margins for general spectral rectangle 316. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0316
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5031926832, 4859017793, 4694051499, 4536561158, 4386113538, 4242306042, 4104764087, 3973138755, 3847104685, 3726358175, 3610615467, 3499611190, 3393096957, 3290840083, 3192622417, 3098239280, 3007498494, 2920219490, 2836232492, 2755377769, 2677504944, 2602472364, 2530146508, 2460401453, 2393118374, 2328185082, 2265495598, 2204949754, 2146452831, 2089915214, 2035252076, 1982383086, 1931232129, 1881727059, 1833799452, 1787384391, 1742420254, 1698848525, 1656613609, 1615662665, 1575945449, 1537414162, 1500023318, 1463729606, 1428491776, 1394270520, 1361028366, 1328729578, 1297340063, 1266827280, 1237160156, 1208309011, 1180245482, 1152942454, 1126373996, 1100515298, 1075342613, 1050833203, 1026965290, 1003718003, 981071337, 959006106, 937503903, 916547066, 896118634, 876202322, 856782479, 837844065, 819372619, 801354229, 783775514, 766623589, 749886052, 733550955, 717606785, 702042447, 686847241, 672010848, 657523311, 643375021, 629556700, 616059387, 602874425, 589993449, 577408370, 565111370, 553094884, 541351592, 529874411, 518656484, 507691169, 496972033, 486492844, 476247561, 466230326, 456435462, 446857460, 437490976, 428330825, 419371973, 410609532, 402038758, 393655041, 385453901, 377430988, 369582071, 361903039, 354389892, 347038743, 339845808, 332807409, 325919962, 319179984, 312584082, 306128951, 299811375, 293628222, 287576439, 281653054, 275855169, 270179961]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 316).prefactor = (2475240021787913/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 316).cutoff/(generalMeanRows 316).c)).2 =
    (12863636621361/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 316).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 316).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 316).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 316

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 316).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 316).criticalRate j.val*(generalMeanRows 316).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 316).c*(generalMeanRows 316).criticalPoint j.val)).2-
      (generalMeanRows 316).J/2-(generalMeanRows 316).error (generalMeanGrid j.val)+
      (generalMeanRows 316).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 316).c)).2-
      (generalMeanRows 316).J/2-(generalMeanRows 316).error 4 := by
  have he : (generalMeanRows 316).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 316) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 316)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0316

/-! Kernel-checked entropy margins for general spectral rectangle 317. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0317
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5152838728, 4978361518, 4811869063, 4652891691, 4500993533, 4355769572, 4216843000, 4083862858, 3956501909, 3834454726, 3717435964, 3605178793, 3497433484, 3393966115, 3294557399, 3199001612, 3107105613, 3018687946, 2933578023, 2851615360, 2772648894, 2696536335, 2623143581, 2552344174, 2484018795, 2418054805, 2354345808, 2292791258, 2233296086, 2175770355, 2120128947, 2066291259, 2014180934, 1963725597, 1914856620, 1867508896, 1821620633, 1777133155, 1733990725, 1692140371, 1651531727, 1612116887, 1573850264, 1536688457, 1500590131, 1465515904, 1431428234, 1398291322, 1366071016, 1334734722, 1304251318, 1274591080, 1245725603, 1217627734, 1190271505, 1163632073, 1137685661, 1112409501, 1087781786, 1063781622, 1040388974, 1017584635, 995350175, 973667906, 952520848, 931892691, 911767763, 892131002, 872967925, 854264599, 836007619, 818184080, 800781555, 783788073, 767192098, 750982511, 735148588, 719679985, 704566718, 689799153, 675367983, 661264222, 647479184, 634004475, 620831978, 607953843, 595362474, 583050522, 571010872, 559236631, 547721128, 536457894, 525440662, 514663356, 504120085, 493805134, 483712957, 473838173, 464175560, 454720044, 445466701, 436410746, 427547530, 418872533, 410381364, 402069752, 393933543, 385968699, 378171288, 370537486, 363063571, 355745918, 348580999, 341565378, 334695709, 327968731, 321381267, 314930222, 308612579, 302425397, 296365807]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 317).prefactor = (199288964093019/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 317).cutoff/(generalMeanRows 317).c)).2 =
    (83865743501341/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 317).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 317).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 317).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 317

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 317).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 317).criticalRate j.val*(generalMeanRows 317).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 317).c*(generalMeanRows 317).criticalPoint j.val)).2-
      (generalMeanRows 317).J/2-(generalMeanRows 317).error (generalMeanGrid j.val)+
      (generalMeanRows 317).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 317).c)).2-
      (generalMeanRows 317).J/2-(generalMeanRows 317).error 4 := by
  have he : (generalMeanRows 317).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 317) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 317)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0317

/-! Kernel-checked entropy margins for general spectral rectangle 318. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0318
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6094005125, 5886463822, 5688270389, 5498889976, 5317825487, 5144614289, 4978825272, 4820056220, 4667931452, 4522099697, 4382232179, 4248020888, 4119176999, 3995429457, 3876523670, 3762220322, 3652294297, 3546533680, 3444738852, 3346721651, 3252304606, 3161320226, 3073610350, 2989025542, 2907424534, 2828673707, 2752646616, 2679223542, 2608291084, 2539741769, 2473473701, 2409390226, 2347399624, 2287414814, 2229353094, 2173135881, 2118688477, 2065939850, 2014822430, 1965271907, 1917227061, 1870629584, 1825423922, 1781557129, 1738978721, 1697640550, 1657496674, 1618503243, 1580618389, 1543802122, 1508016232, 1473224198, 1439391103, 1406483547, 1374469576, 1343318605, 1313001353, 1283489774, 1254757001, 1226777281, 1199525930, 1172979271, 1147114593, 1121910100, 1097344870, 1073398813, 1050052630, 1027287778, 1005086434, 983431460, 962306376, 941695324, 921583044, 901954846, 882796581, 864094624, 845835843, 828007582, 810597639, 793594245, 776986048, 760762091, 744911799, 729424962, 714291716, 699502534, 685048208, 670919837, 657108814, 643606817, 630405792, 617497946, 604875737, 592531860, 580459242, 568651033, 557100593, 545801486, 534747476, 523932514, 513350732, 502996440, 492864114, 482948395, 473244077, 463746109, 454449583, 445349731, 436441920, 427721650, 419184543, 410826345, 402642919, 394630240, 386784395, 379101573, 371578068, 364210271, 356994671, 349927847, 343006469]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 318).prefactor = (561069098345191/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 318).cutoff/(generalMeanRows 318).c)).2 =
    (190718805137309/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 318).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 318).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 318).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 318

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 318).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 318).criticalRate j.val*(generalMeanRows 318).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 318).c*(generalMeanRows 318).criticalPoint j.val)).2-
      (generalMeanRows 318).J/2-(generalMeanRows 318).error (generalMeanGrid j.val)+
      (generalMeanRows 318).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 318).c)).2-
      (generalMeanRows 318).J/2-(generalMeanRows 318).error 4 := by
  have he : (generalMeanRows 318).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 318) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 318)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0318

/-! Kernel-checked entropy margins for general spectral rectangle 319. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0319
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5021632663, 4846591799, 4679594064, 4520169390, 4367881370, 4222324314, 4083120632, 3949918480, 3822389647, 3700227653, 3583146033, 3470876782, 3363168944, 3259787331, 3160511356, 3065133969, 2973460681, 2885308675, 2800505990, 2718890766, 2640310562, 2564621712, 2491688745, 2421383842, 2353586337, 2288182257, 2225063887, 2164129381, 2105282391, 2048431722, 1993491020, 1940378470, 1889016526, 1839331652, 1791254084, 1744717603, 1699659336, 1656019550, 1613741478, 1572771148, 1533057220, 1494550840, 1457205502, 1420976913, 1385822873, 1351703158, 1318579416, 1286415060, 1255175178, 1224826437, 1195337008, 1166676477, 1138815777, 1111727115, 1085383907, 1059760716, 1034833192, 1010578018, 986972856, 963996302, 941627835, 919847776, 898637243, 877978118, 857853006, 838245200, 819138648, 800517925, 782368200, 764675209, 747425230, 730605055, 714201971, 698203732, 682598541, 667375032, 652522244, 638029611, 623886938, 610084389, 596612470, 583462014, 570624169, 558090380, 545852382, 533902184, 522232062, 510834541, 499702393, 488828621, 478206452, 467829327, 457690896, 447785005, 438105692, 428647177, 419403857, 410370300, 401541234, 392911547, 384476277, 376230608, 368169864, 360289506, 352585124, 345052433, 337687273, 330485597, 323443474, 316557083, 309822704, 303236725, 296795628, 290495992, 284334488, 278307877, 272413005, 266646801, 261006276, 255488520, 250090696]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 319).prefactor = (2495601788718903/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 319).cutoff/(generalMeanRows 319).c)).2 =
    (99499180742067/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 319).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 319).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 319).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 319

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 319).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 319).criticalRate j.val*(generalMeanRows 319).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 319).c*(generalMeanRows 319).criticalPoint j.val)).2-
      (generalMeanRows 319).J/2-(generalMeanRows 319).error (generalMeanGrid j.val)+
      (generalMeanRows 319).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 319).c)).2-
      (generalMeanRows 319).J/2-(generalMeanRows 319).error 4 := by
  have he : (generalMeanRows 319).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 319) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 319)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0319

/-! Kernel-checked entropy margins for general spectral rectangle 320. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0320
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5895613769, 5686384360, 5486644373, 5295854435, 5113513057, 4939153327, 4772339966, 4612666688, 4459753840, 4313246271, 4172811414, 4038137550, 3908932235, 3784920869, 3665845398, 3551463124, 3441545621, 3335877743, 3234256713, 3136491287, 3042400981, 2951815369, 2864573420, 2780522903, 2699519823, 2621427903, 2546118107, 2473468195, 2403362308, 2335690585, 2270348802, 2207238044, 2146264390, 2087338624, 2030375964, 1975295811, 1922021510, 1870480129, 1820602252, 1772321784, 1725575770, 1680304222, 1636449960, 1593958461, 1552777718, 1512858104, 1474152250, 1436614926, 1400202928, 1364874976, 1330591615, 1297315121, 1265009415, 1233639976, 1203173770, 1173579171, 1144825891, 1116884920, 1089728456, 1063329852, 1037663559, 1012705072, 988430881, 964818424, 941846043, 919492940, 897739138, 876565445, 855953413, 835885308, 816344076, 797313315, 778777239, 760720658, 743128947, 725988024, 709284322, 693004770, 677136773, 661668186, 646587298, 631882816, 617543842, 603559859, 589920718, 576616617, 563638091, 550975994, 538621494, 526566049, 514801405, 503319580, 492112853, 481173757, 470495064, 460069780, 449891133, 439952567, 430247733, 420770479, 411514845, 402475056, 393645512, 385020786, 376595614, 368364890, 360323663, 352467125, 344790615, 337289605, 329959700, 322796632, 315796258, 308954551, 302267601, 295731607, 289342876, 283097817, 276992940, 271024852, 265190253]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 320).prefactor = (1416855928530339/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 320).cutoff/(generalMeanRows 320).c)).2 =
    (70273978341811/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 320).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 320).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 320).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 320

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 320).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 320).criticalRate j.val*(generalMeanRows 320).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 320).c*(generalMeanRows 320).criticalPoint j.val)).2-
      (generalMeanRows 320).J/2-(generalMeanRows 320).error (generalMeanGrid j.val)+
      (generalMeanRows 320).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 320).c)).2-
      (generalMeanRows 320).J/2-(generalMeanRows 320).error 4 := by
  have he : (generalMeanRows 320).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 320) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 320)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0320

/-! Kernel-checked entropy margins for general spectral rectangle 321. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0321
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5221869338, 5049927699, 4885770977, 4728942136, 4579017037, 4435601559, 4298329033, 4166857939, 4040869841, 3920067520, 3804173301, 3692927519, 3586087151, 3483424550, 3384726313, 3289792227, 3198434325, 3110476010, 3025751254, 2944103868, 2865386821, 2789461623, 2716197747, 2645472106, 2577168560, 2511177465, 2447395254, 2385724051, 2326071308, 2268349475, 2212475684, 2158371465, 2105962478, 2055178256, 2005951980, 1958220255, 1911922912, 1867002815, 1823405683, 1781079931, 1739976506, 1700048748, 1661252253, 1623544747, 1586885961, 1551237528, 1516562871, 1482827109, 1449996961, 1418040663, 1386927882, 1356629644, 1327118259, 1298367254, 1270351307, 1243046193, 1216428719, 1190476678, 1165168794, 1140484678, 1116404779, 1092910348, 1069983391, 1047606640, 1025763509, 1004438066, 983614999, 963279588, 943417675, 924015639, 905060368, 886539239, 868440092, 850751210, 833461298, 816559468, 800035211, 783878393, 768079226, 752628262, 737516372, 722734737, 708274830, 694128408, 680287496, 666744379, 653491589, 640521896, 627828297, 615404010, 603242460, 591337276, 579682277, 568271472, 557099047, 546159358, 535446930, 524956443, 514682734, 504620784, 494765717, 485112795, 475657412, 466395086, 457321460, 448432296, 439723468, 431190963, 422830871, 414639387, 406612805, 398747516, 391040003, 383486838, 376084681, 368830276, 361720449, 354752105, 347922224, 341227862, 334666145]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 321).prefactor = (1220979017071971/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 321).cutoff/(generalMeanRows 321).c)).2 =
    (85866286635753/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 321).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 321).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 321).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 321

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 321).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 321).criticalRate j.val*(generalMeanRows 321).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 321).c*(generalMeanRows 321).criticalPoint j.val)).2-
      (generalMeanRows 321).J/2-(generalMeanRows 321).error (generalMeanGrid j.val)+
      (generalMeanRows 321).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 321).c)).2-
      (generalMeanRows 321).J/2-(generalMeanRows 321).error 4 := by
  have he : (generalMeanRows 321).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 321) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 321)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0321

/-! Kernel-checked entropy margins for general spectral rectangle 322. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0322
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5021988035, 4849131324, 4684187979, 4526694731, 4376221553, 4232368764, 4094764431, 3963062045, 3836938436, 3716091886, 3600240439, 3489120356, 3382484728, 3280102202, 3181755834, 3087242029, 2996369584, 2908958806, 2824840701, 2743856237, 2665855660, 2590697864, 2518249816, 2448386019, 2380988020, 2315943951, 2253148110, 2192500567, 2133906797, 2077277350, 2022527530, 1969577109, 1918350051, 1868774260, 1820781347, 1774306407, 1729287815, 1685667034, 1643388434, 1602399130, 1562648818, 1524089633, 1486676011, 1450364559, 1415113933, 1380884729, 1347639374, 1315342025, 1283958478, 1253456079, 1223803640, 1194971363, 1166930766, 1139654614, 1113116853, 1087292554, 1062157847, 1037689875, 1013866737, 990667445, 968071873, 946060718, 924615458, 903718315, 883352217, 863500764, 844148199, 825279373, 806879719, 788935223, 771432401, 754358270, 737700331, 721446540, 705585292, 690105403, 674996084, 660246930, 645847902, 631789308, 618061791, 604656314, 591564146, 578776849, 566286265, 554084505, 542163940, 530517186, 519137099, 508016760, 497149471, 486528742, 476148287, 466002013, 456084012, 446388558, 436910095, 427643234, 418582746, 409723556, 401060735, 392589501, 384305206, 376203336, 368279504, 360529447, 352949024, 345534203, 338281069, 331185811, 324244722, 317454195, 310810722, 304310887, 297951364, 291728915, 285640389, 279682713, 273852898, 268148029, 262565267]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 322).prefactor = (4946643410390047/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 322).cutoff/(generalMeanRows 322).c)).2 =
    (203214834446041/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 322).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 322).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 322).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 322

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 322).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 322).criticalRate j.val*(generalMeanRows 322).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 322).c*(generalMeanRows 322).criticalPoint j.val)).2-
      (generalMeanRows 322).J/2-(generalMeanRows 322).error (generalMeanGrid j.val)+
      (generalMeanRows 322).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 322).c)).2-
      (generalMeanRows 322).J/2-(generalMeanRows 322).error 4 := by
  have he : (generalMeanRows 322).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 322) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 322)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0322

/-! Kernel-checked entropy margins for general spectral rectangle 323. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0323
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7000709966, 6803256498, 6613947818, 6432343636, 6258034066, 6090636920, 5929795305, 5775175487, 5626464980, 5483370835, 5345618103, 5212948449, 5085118899, 4961900710, 4843078336, 4728448495, 4617819313, 4511009545, 4407847861, 4308172185, 4211829102, 4118673296, 4028567042, 3941379734, 3856987449, 3775272541, 3696123270, 3619433448, 3545102123, 3473033273, 3403135527, 3335321904, 3269509566, 3205619595, 3143576775, 3083309393, 3024749055, 2967830504, 2912491461, 2858672467, 2806316738, 2755370028, 2705780500, 2657498606, 2610476968, 2564670277, 2520035184, 2476530208, 2434115645, 2392753481, 2352407309, 2313042256, 2274624908, 2237123241, 2200506556, 2164745418, 2129811596, 2095678008, 2062318669, 2029708640, 1997823979, 1966641700, 1936139726, 1906296848, 1877092692, 1848507675, 1820522974, 1793120490, 1766282821, 1739993225, 1714235596, 1688994437, 1664254830, 1640002413, 1616223358, 1592904346, 1570032546, 1547595596, 1525581580, 1503979012, 1482776818, 1461964318, 1441531209, 1421467552, 1401763755, 1382410558, 1363399023, 1344720516, 1326366701, 1308329521, 1290601193, 1273174193, 1256041247, 1239195323, 1222629616, 1206337546, 1190312745, 1174549049, 1159040491, 1143781294, 1128765862, 1113988773, 1099444776, 1085128778, 1071035844, 1057161189, 1043500172, 1030048290, 1016801173, 1003754581, 990904399, 978246628, 965777388, 953492906, 941389519, 929463665, 917711882, 906130804, 894717156, 883467754, 872379500]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 323).prefactor = (4599540156782783/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 323).cutoff/(generalMeanRows 323).c)).2 =
    (19587159813917/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 323).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 323).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 323).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 323

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 323).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 323).criticalRate j.val*(generalMeanRows 323).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 323).c*(generalMeanRows 323).criticalPoint j.val)).2-
      (generalMeanRows 323).J/2-(generalMeanRows 323).error (generalMeanGrid j.val)+
      (generalMeanRows 323).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 323).c)).2-
      (generalMeanRows 323).J/2-(generalMeanRows 323).error 4 := by
  have he : (generalMeanRows 323).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 323) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 323)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0323

/-! Kernel-checked entropy margins for general spectral rectangle 324. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0324
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7193800669, 6987222559, 6789170115, 6599183202, 6416833450, 6241721423, 6073474115, 5911742710, 5756200592, 5606541553, 5462478188, 5323740448, 5190074329, 5061240693, 4937014187, 4817182268, 4701544310, 4589910788, 4482102532, 4377950043, 4277292862, 4179978992, 4085864368, 3994812355, 3906693302, 3821384115, 3738767864, 3658733425, 3581175138, 3505992494, 3433089843, 3362376119, 3293764588, 3227172606, 3162521399, 3099735852, 3038744317, 2979478424, 2921872914, 2865865476, 2811396591, 2758409395, 2706849540, 2656665070, 2607806299, 2560225700, 2513877796, 2468719065, 2424707839, 2381804218, 2339969984, 2299168521, 2259364739, 2220525002, 2182617060, 2145609983, 2109474104, 2074180956, 2039703219, 2006014669, 1973090125, 1940905405, 1909437281, 1878663434, 1848562414, 1819113606, 1790297186, 1762094092, 1734485988, 1707455234, 1680984853, 1655058508, 1629660467, 1604775584, 1580389269, 1556487470, 1533056643, 1510083737, 1487556171, 1465461814, 1443788966, 1422526342, 1401663053, 1381188592, 1361092815, 1341365930, 1321998480, 1302981331, 1284305658, 1265962934, 1247944916, 1230243637, 1212851390, 1195760723, 1178964427, 1162455526, 1146227267, 1130273115, 1114586740, 1099162013, 1083992995, 1069073934, 1054399253, 1039963547, 1025761574, 1011788253, 998038651, 984507986, 971191613, 958085028, 945183853, 932483839, 919980859, 907670903, 895550072, 883614578, 871860739, 860284973, 848883795, 837653818, 826591742]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 324).prefactor = (601395770195373/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 324).cutoff/(generalMeanRows 324).c)).2 =
    (76328420058367/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 324).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 324).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 324).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 324

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 324).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 324).criticalRate j.val*(generalMeanRows 324).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 324).c*(generalMeanRows 324).criticalPoint j.val)).2-
      (generalMeanRows 324).J/2-(generalMeanRows 324).error (generalMeanGrid j.val)+
      (generalMeanRows 324).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 324).c)).2-
      (generalMeanRows 324).J/2-(generalMeanRows 324).error 4 := by
  have he : (generalMeanRows 324).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 324) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 324)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0324

/-! Kernel-checked entropy margins for general spectral rectangle 325. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0325
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7393273135, 7177227756, 6970107013, 6771429975, 6580748896, 6397646266, 6221732184, 6052642025, 5890034355, 5733589063, 5583005680, 5438001871, 5298312062, 5163686209, 5033888668, 4908697180, 4787901931, 4671304706, 4558718107, 4449964837, 4344877046, 4243295722, 4145070135, 4050057324, 3958121618, 3869134199, 3782972687, 3699520768, 3618667836, 3540308666, 3464343112, 3390675813, 3319215937, 3249876924, 3182576260, 3117235252, 3053778829, 2992135350, 2932236419, 2874016725, 2817413875, 2762368249, 2708822859, 2656723214, 2606017199, 2556654956, 2508588770, 2461772969, 2416163819, 2371719439, 2328399702, 2286166160, 2244981959, 2204811768, 2165621704, 2127379267, 2090053278, 2053613812, 2018032147, 1983280707, 1949333008, 1916163613, 1883748081, 1852062925, 1821085570, 1790794310, 1761168275, 1732187387, 1703832332, 1676084525, 1648926077, 1622339766, 1596309009, 1570817835, 1545850858, 1521393253, 1497430732, 1473949522, 1450936344, 1428378390, 1406263307, 1384579177, 1363314498, 1342458166, 1321999464, 1301928041, 1282233900, 1262907383, 1243939156, 1225320200, 1207041795, 1189095509, 1171473188, 1154166941, 1137169138, 1120472390, 1104069547, 1087953685, 1072118099, 1056556295, 1041261979, 1026229055, 1011451610, 996923914, 982640410, 968595707, 954784577, 941201945, 927842885, 914702616, 901776496, 889060015, 876548793, 864238573, 852125219, 840204709, 828473135, 816926694, 805561688, 794374518, 783361683]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 325).prefactor = (5032529132294703/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 325).cutoff/(generalMeanRows 325).c)).2 =
    (185821008478627/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 325).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 325).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 325).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 325

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 325).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 325).criticalRate j.val*(generalMeanRows 325).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 325).c*(generalMeanRows 325).criticalPoint j.val)).2-
      (generalMeanRows 325).J/2-(generalMeanRows 325).error (generalMeanGrid j.val)+
      (generalMeanRows 325).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 325).c)).2-
      (generalMeanRows 325).J/2-(generalMeanRows 325).error 4 := by
  have he : (generalMeanRows 325).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 325) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 325)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0325

/-! Kernel-checked entropy margins for general spectral rectangle 326. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0326
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6328227032, 6107786905, 5896755884, 5694631636, 5500946264, 5315263248, 5137174720, 4966299043, 4802278654, 4644778122, 4493482408, 4348095299, 4208337989, 4073947799, 3944677010, 3820291806, 3700571304, 3585306679, 3474300348, 3367365236, 3264324091, 3165008860, 3069260111, 2976926500, 2887864280, 2801936840, 2719014288, 2638973054, 2561695528, 2487069716, 2414988930, 2345351486, 2278060435, 2213023298, 2150151832, 2089361803, 2030572769, 1973707890, 1918693736, 1865460114, 1813939903, 1764068900, 1715785676, 1669031433, 1623749883, 1579887118, 1537391499, 1496213548, 1456305841, 1417622914, 1380121173, 1343758801, 1308495679, 1274293309, 1241114738, 1208924489, 1177688493, 1147374027, 1117949653, 1089385162, 1061651520, 1034720814, 1008566207, 983161888, 958483031, 934505748, 911207054, 888564826, 866557766, 845165368, 824367886, 804146298, 784482280, 765358176, 746756970, 728662261, 711058236, 693929649, 677261796, 661040496, 645252064, 629883299, 614921461, 600354252, 586169800, 572356642, 558903709, 545800311, 533036119, 520601155, 508485777, 496680667, 485176817, 473965519, 463038353, 452387178, 442004117, 431881552, 422012112, 412388666, 403004311, 393852365, 384926362, 376220040, 367727333, 359442371, 351359464, 343473101, 335777944, 328268818, 320940709, 313788756, 306808248, 299994615, 293343428, 286850390, 280511334, 274322218, 268279119, 262378231, 256615861]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 326).prefactor = (658009633655201/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 326).cutoff/(generalMeanRows 326).c)).2 =
    (64711630702977/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 326).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 326).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 326).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 326

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 326).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 326).criticalRate j.val*(generalMeanRows 326).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 326).c*(generalMeanRows 326).criticalPoint j.val)).2-
      (generalMeanRows 326).J/2-(generalMeanRows 326).error (generalMeanGrid j.val)+
      (generalMeanRows 326).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 326).c)).2-
      (generalMeanRows 326).J/2-(generalMeanRows 326).error 4 := by
  have he : (generalMeanRows 326).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 326) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 326)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0326

/-! Kernel-checked entropy margins for general spectral rectangle 327. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0327
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6597627299, 6394029168, 6199027573, 6012153438, 5832970136, 5661070628, 5496074913, 5337627761, 5185396676, 5039070078, 4898355660, 4762978912, 4632681780, 4507221452, 4386369259, 4269909668, 4157639368, 4049366428, 3944909535, 3844097282, 3746767529, 3652766797, 3561949726, 3474178563, 3389322691, 3307258195, 3227867460, 3151038794, 3076666079, 3004648449, 2934889986, 2867299438, 2801789961, 2738278864, 2676687388, 2616940488, 2558966629, 2502697599, 2448068335, 2395016750, 2343483584, 2293412251, 2244748703, 2197441302, 2151440695, 2106699699, 2063173191, 2020818009, 1979592849, 1939458182, 1900376157, 1862310528, 1825226572, 1789091018, 1753871975, 1719538872, 1686062388, 1653414400, 1621567923, 1590497060, 1560176950, 1530583721, 1501694443, 1473487091, 1445940495, 1419034311, 1392748976, 1367065679, 1341966325, 1317433503, 1293450457, 1270001057, 1247069774, 1224641649, 1202702273, 1181237762, 1160234733, 1139680286, 1119561980, 1099867817, 1080586220, 1061706020, 1043216434, 1025107052, 1007367822, 989989034, 972961306, 956275573, 939923072, 923895328, 908184149, 892781608, 877680036, 862872011, 848350349, 834108093, 820138507, 806435065, 792991443, 779801514, 766859338, 754159154, 741695377, 729462589, 717455532, 705669104, 694098353, 682738470, 671584785, 660632762, 649877995, 639316200, 628943215, 618754994, 608747600, 598917207, 589260090, 579772629, 570451295, 561292657, 552293374]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 327).prefactor = (4938505327506623/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 327).cutoff/(generalMeanRows 327).c)).2 =
    (364042442962821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 327).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 327).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 327).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 327

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 327).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 327).criticalRate j.val*(generalMeanRows 327).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 327).c*(generalMeanRows 327).criticalPoint j.val)).2-
      (generalMeanRows 327).J/2-(generalMeanRows 327).error (generalMeanGrid j.val)+
      (generalMeanRows 327).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 327).c)).2-
      (generalMeanRows 327).J/2-(generalMeanRows 327).error 4 := by
  have he : (generalMeanRows 327).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 327) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 327)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0327

/-! Kernel-checked entropy margins for general spectral rectangle 328. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0328
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6118638473, 5935582216, 5760353076, 5592514352, 5431659824, 5277411075, 5129415116, 4987342257, 4850884203, 4719752346, 4593676221, 4472402115, 4355691806, 4243321420, 4135080386, 4030770491, 3930205011, 3833207922, 3739613165, 3649263986, 3562012318, 3477718216, 3396249334, 3317480445, 3241292993, 3167574679, 3096219081, 3027125296, 2960197609, 2895345186, 2832481788, 2771525503, 2712398498, 2655026783, 2599339999, 2545271208, 2492756709, 2441735854, 2392150884, 2343946772, 2297071072, 2251473787, 2207107233, 2163925920, 2121886435, 2080947338, 2041069052, 2002213776, 1964345389, 1927429363, 1891432688, 1856323792, 1822072469, 1788649815, 1756028158, 1724181000, 1693082963, 1662709728, 1633037991, 1604045407, 1575710549, 1548012864, 1520932630, 1494450915, 1468549545, 1443211066, 1418418709, 1394156361, 1370408534, 1347160334, 1324397439, 1302106069, 1280272962, 1258885353, 1237930950, 1217397913, 1197274834, 1177550721, 1158214974, 1139257373, 1120668060, 1102437523, 1084556580, 1067016369, 1049808328, 1032924191, 1016355966, 1000095932, 984136620, 968470811, 953091518, 937991982, 923165660, 908606215, 894307513, 880263610, 866468745, 852917335, 839603967, 826523390, 813670512, 801040390, 788628228, 776429366, 764439282, 752653583, 741067998, 729678379, 718480690, 707471010, 696645522, 686000514, 675532375, 665237587, 655112727, 645154460, 635359540, 625724802, 616247161, 606923613, 597751226]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 328).prefactor = (184818068964103/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 328).cutoff/(generalMeanRows 328).c)).2 =
    (203200858400981/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 328).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 328).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 328).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 328

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 328).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 328).criticalRate j.val*(generalMeanRows 328).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 328).c*(generalMeanRows 328).criticalPoint j.val)).2-
      (generalMeanRows 328).J/2-(generalMeanRows 328).error (generalMeanGrid j.val)+
      (generalMeanRows 328).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 328).c)).2-
      (generalMeanRows 328).J/2-(generalMeanRows 328).error 4 := by
  have he : (generalMeanRows 328).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 328) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 328)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0328

/-! Kernel-checked entropy margins for general spectral rectangle 329. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0329
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6115875708, 5926751922, 5745747528, 5572410859, 5406321730, 5247088678, 5094346498, 4947754055, 4806992310, 4671762559, 4541784839, 4416796488, 4296550848, 4180816075, 4069374074, 3962019512, 3858558925, 3758809900, 3662600322, 3569767690, 3480158475, 3393627541, 3310037606, 3229258743, 3151167918, 3075648569, 3002590203, 2931888034, 2863442639, 2797159644, 2732949423, 2670726828, 2610410927, 2551924765, 2495195143, 2440152402, 2386730232, 2334865484, 2284497998, 2235570444, 2188028167, 2141819042, 2096893345, 2053203626, 2010704584, 1969352965, 1929107446, 1889928547, 1851778527, 1814621302, 1778422362, 1743148688, 1708768681, 1675252091, 1642569953, 1610694519, 1579599203, 1549258526, 1519648057, 1490744369, 1462524988, 1434968349, 1408053753, 1381761325, 1356071978, 1330967377, 1306429901, 1282442612, 1258989225, 1236054078, 1213622101, 1191678793, 1170210196, 1149202869, 1128643867, 1108520717, 1088821401, 1069534331, 1050648336, 1032152641, 1014036848, 996290926, 978905188, 961870284, 945177179, 928817147, 912781754, 897062848, 881652546, 866543221, 851727499, 837198240, 822948534, 808971691, 795261231, 781810875, 768614540, 755666331, 742960530, 730491594, 718254144, 706242962, 694452984, 682879294, 671517118, 660361819, 649408893, 638653962, 628092773, 617721189, 607535189, 597530859, 587704394, 578052091, 568570344, 559255646, 550104577, 541113810, 532280103, 523600297, 515071312]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 329).prefactor = (2391128907780723/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 329).cutoff/(generalMeanRows 329).c)).2 =
    (388702139702561/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 329).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 329).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 329).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 329

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 329).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 329).criticalRate j.val*(generalMeanRows 329).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 329).c*(generalMeanRows 329).criticalPoint j.val)).2-
      (generalMeanRows 329).J/2-(generalMeanRows 329).error (generalMeanGrid j.val)+
      (generalMeanRows 329).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 329).c)).2-
      (generalMeanRows 329).J/2-(generalMeanRows 329).error 4 := by
  have he : (generalMeanRows 329).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 329) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 329)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0329

/-! Kernel-checked entropy margins for general spectral rectangle 330. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0330
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5859350950, 5678103444, 5504699744, 5338698841, 5179690624, 5027293179, 4881150383, 4740929745, 4606320481, 4477031773, 4352791211, 4233343373, 4118448549, 4007881572, 3901430768, 3798896981, 3700092700, 3604841246, 3512976035, 3424339897, 3338784450, 3256169528, 3176362644, 3099238503, 3024678547, 2952570534, 2882808149, 2815290640, 2749922485, 2686613075, 2625276427, 2565830911, 2508198995, 2452307010, 2398084931, 2345466167, 2294387370, 2244788256, 2196611430, 2149802233, 2104308589, 2060080867, 2017071749, 1975236106, 1934530883, 1894914988, 1856349193, 1818796031, 1782219709, 1746586023, 1711862274, 1678017191, 1645020864, 1612844668, 1581461207, 1550844246, 1520968659, 1491810371, 1463346309, 1435554352, 1408413285, 1381902757, 1356003237, 1330695979, 1305962981, 1281786953, 1258151281, 1235039997, 1212437751, 1190329779, 1168701879, 1147540383, 1126832135, 1106564467, 1086725177, 1067302510, 1048285133, 1029662125, 1011422950, 993557446, 976055808, 958908570, 942106594, 925641052, 909503418, 893685450, 878179181, 862976910, 848071183, 833454793, 819120762, 805062336, 791272974, 777746341, 764476297, 751456893, 738682361, 726147108, 713845709, 701772899, 689923571, 678292764, 666875664, 655667592, 644664006, 633860488, 623252748, 612836611, 602608020, 592563028, 582697792, 573008575, 563491740, 554143742, 544961133, 535940551, 527078722, 518372456, 509818643, 501414250, 493156322]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 330).prefactor = (1171618801852349/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 330).cutoff/(generalMeanRows 330).c)).2 =
    (401947366452581/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 330).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 330).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 330).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 330

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 330).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 330).criticalRate j.val*(generalMeanRows 330).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 330).c*(generalMeanRows 330).criticalPoint j.val)).2-
      (generalMeanRows 330).J/2-(generalMeanRows 330).error (generalMeanGrid j.val)+
      (generalMeanRows 330).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 330).c)).2-
      (generalMeanRows 330).J/2-(generalMeanRows 330).error 4 := by
  have he : (generalMeanRows 330).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 330) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 330)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0330

/-! Kernel-checked entropy margins for general spectral rectangle 331. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0331
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5615508312, 5442369148, 5276776801, 5118302008, 4966545787, 4821136785, 4681728924, 4547999286, 4419646227, 4296387667, 4177959559, 4064114500, 3954620469, 3849259688, 3747827577, 3650131811, 3555991443, 3465236119, 3377705345, 3293247818, 3211720812, 3132989613, 3056926990, 2983412719, 2912333131, 2843580703, 2777053670, 2712655671, 2650295420, 2589886396, 2531346561, 2474598088, 2419567116, 2366183518, 2314380687, 2264095326, 2215267269, 2167839294, 2121756968, 2076968480, 2033424506, 1991078066, 1949884398, 1909800838, 1870786705, 1832803197, 1795813291, 1759781646, 1724674519, 1690459676, 1657106320, 1624585011, 1592867601, 1561927164, 1531737937, 1502275261, 1473515523, 1445436107, 1418015344, 1391232463, 1365067549, 1339501502, 1314515995, 1290093438, 1266216943, 1242870290, 1220037896, 1197704784, 1175856554, 1154479360, 1133559878, 1113085287, 1093043245, 1073421865, 1054209697, 1035395706, 1016969256, 998920089, 981238312, 963914379, 946939073, 930303498, 913999061, 898017458, 882350665, 866990924, 851930733, 837162834, 822680204, 808476045, 794543774, 780877015, 767469590, 754315514, 741408983, 728744368, 716316211, 704119215, 692148238, 680398291, 668864526, 657542236, 646426847, 635513913, 624799113, 614278245, 603947221, 593802066, 583838909, 574053984, 564443625, 555004261, 545732413, 536624693, 527677799, 518888512, 510253693, 501770284, 493435299, 485245828, 477199030]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 331).prefactor = (4581599392280411/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 331).cutoff/(generalMeanRows 331).c)).2 =
    (208725776494273/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 331).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 331).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 331).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 331

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 331).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 331).criticalRate j.val*(generalMeanRows 331).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 331).c*(generalMeanRows 331).criticalPoint j.val)).2-
      (generalMeanRows 331).J/2-(generalMeanRows 331).error (generalMeanGrid j.val)+
      (generalMeanRows 331).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 331).c)).2-
      (generalMeanRows 331).J/2-(generalMeanRows 331).error 4 := by
  have he : (generalMeanRows 331).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 331) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 331)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0331

/-! Kernel-checked entropy margins for general spectral rectangle 332. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0332
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4886640276, 4712298957, 4545817639, 4386753114, 4234693173, 4089253905, 3950077282, 3816829005, 3689196573, 3566887536, 3449627933, 3337160869, 3229245231, 3125654518, 3026175783, 2930608655, 2838764460, 2750465407, 2665543845, 2583841580, 2505209243, 2429505718, 2356597601, 2286358711, 2218669631, 2153417287, 2090494555, 2029799900, 1971237033, 1914714603, 1860145900, 1807448586, 1756544435, 1707359103, 1659821903, 1613865598, 1569426206, 1526442822, 1484857444, 1444614819, 1405662288, 1367949651, 1331429029, 1296054749, 1261783220, 1228572827, 1196383828, 1165178256, 1134919831, 1105573869, 1077107205, 1049488114, 1022686241, 996672532, 971419166, 946899504, 923088019, 899960252, 877492756, 855663046, 834449558, 813831601, 793789318, 774303646, 755356281, 736929638, 719006825, 701571605, 684608370, 668102111, 652038392, 636403322, 621183535, 606366163, 591938817, 577889562, 564206903, 550879760, 537897457, 525249698, 512926555, 500918451, 489216146, 477810723, 466693574, 455856388, 445291138, 434990071, 424945693, 415150767, 405598291, 396281499, 387193848, 378329006, 369680849, 361243450, 353011072, 344978162, 337139341, 329489401, 322023296, 314736137, 307623187, 300679853, 293901684, 287284363, 280823702, 274515643, 268356243, 262341681, 256468247, 250732338, 245130458, 239659212, 234315304, 229095529, 223996778, 219016027, 214150338, 209396857, 204752808]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 332).prefactor = (2360793562246847/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 332).cutoff/(generalMeanRows 332).c)).2 =
    (84352211328753/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 332).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 332).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 332).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 332

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 332).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 332).criticalRate j.val*(generalMeanRows 332).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 332).c*(generalMeanRows 332).criticalPoint j.val)).2-
      (generalMeanRows 332).J/2-(generalMeanRows 332).error (generalMeanGrid j.val)+
      (generalMeanRows 332).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 332).c)).2-
      (generalMeanRows 332).J/2-(generalMeanRows 332).error 4 := by
  have he : (generalMeanRows 332).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 332) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 332)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0332

/-! Kernel-checked entropy margins for general spectral rectangle 333. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0333
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5058011154, 4884384014, 4718557647, 4560087479, 4408560266, 4263591360, 4124822275, 3991918503, 3864567554, 3742477197, 3625373870, 3513001244, 3405118913, 3301501220, 3201936170, 3106224452, 3014178540, 2925621866, 2840388070, 2758320307, 2679270606, 2603099285, 2529674410, 2458871293, 2390572032, 2324665078, 2261044844, 2199611332, 2140269790, 2082930402, 2027507981, 1973921702, 1922094841, 1871954535, 1823431561, 1776460123, 1730977663, 1686924670, 1644244514, 1602883285, 1562789643, 1523914673, 1486211759, 1449636455, 1414146370, 1379701059, 1346261920, 1313792094, 1282256377, 1251621133, 1221854212, 1192924877, 1164803728, 1137462636, 1110874678, 1085014080, 1059856154, 1035377251, 1011554705, 988366786, 965792656, 943812325, 922406610, 901557098, 881246107, 861456653, 842172419, 823377721, 805057479, 787197194, 769782912, 752801210, 736239164, 720084331, 704324726, 688948801, 673945426, 659303874, 645013798, 631065219, 617448508, 604154372, 591173839, 578498245, 566119222, 554028682, 542218812, 530682056, 519411108, 508398903, 497638605, 487123596, 476847473, 466804036, 456987279, 447391386, 438010720, 428839818, 419873386, 411106288, 402533546, 394150329, 385951950, 377933861, 370091647, 362421022, 354917822, 347578005, 340397643, 333372920, 326500126, 319775657, 313196006, 306757764, 300457618, 294292342, 288258798, 282353933, 276574776, 270918434, 265382092]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 333).prefactor = (4719818171200337/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 333).cutoff/(generalMeanRows 333).c)).2 =
    (372452249075193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 333).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 333).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 333).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 333

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 333).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 333).criticalRate j.val*(generalMeanRows 333).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 333).c*(generalMeanRows 333).criticalPoint j.val)).2-
      (generalMeanRows 333).J/2-(generalMeanRows 333).error (generalMeanGrid j.val)+
      (generalMeanRows 333).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 333).c)).2-
      (generalMeanRows 333).J/2-(generalMeanRows 333).error 4 := by
  have he : (generalMeanRows 333).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 333) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 333)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0333

/-! Kernel-checked entropy margins for general spectral rectangle 334. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0334
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5194071442, 5020749108, 4855190023, 4696948912, 4545612020, 4400794361, 4262137263, 4129306175, 4001988692, 3879892782, 3762745185, 3650289965, 3542287196, 3438511768, 3338752304, 3242810163, 3150498541, 3061641638, 2976073895, 2893639302, 2814190749, 2737589439, 2663704337, 2592411673, 2523594467, 2457142106, 2392949937, 2330918901, 2270955185, 2212969904, 2156878801, 2102601974, 2050063611, 1999191754, 1949918071, 1902177648, 1855908791, 1811052842, 1767554010, 1725359206, 1684417894, 1644681950, 1606105530, 1568644942, 1532258533, 1496906576, 1462551170, 1429156140, 1396686948, 1365110604, 1334395589, 1304511776, 1275430358, 1247123783, 1219565688, 1192730837, 1166595070, 1141135243, 1116329180, 1092155628, 1068594207, 1045625368, 1023230356, 1001391170, 980090525, 959311820, 939039106, 919257053, 899950922, 881106540, 862710270, 844748988, 827210060, 810081320, 793351049, 777007951, 761041142, 745440124, 730194773, 715295321, 700732339, 686496727, 672579693, 658972749, 645667688, 632656580, 619931757, 607485805, 595311547, 583402043, 571750572, 560350628, 549195909, 538280310, 527597917, 517142995, 506909985, 496893496, 487088299, 477489321, 468091637, 458890467, 449881169, 441059237, 432420292, 423960080, 415674465, 407559428, 399611063, 391825567, 384199246, 376728503, 369409839, 362239847, 355215213, 348332708, 341589189, 334981595, 328506941, 322162324, 315944909]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 334).prefactor = (4718726191479517/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 334).cutoff/(generalMeanRows 334).c)).2 =
    (24639082522417/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 334).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 334).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 334).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 334

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 334).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 334).criticalRate j.val*(generalMeanRows 334).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 334).c*(generalMeanRows 334).criticalPoint j.val)).2-
      (generalMeanRows 334).J/2-(generalMeanRows 334).error (generalMeanGrid j.val)+
      (generalMeanRows 334).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 334).c)).2-
      (generalMeanRows 334).J/2-(generalMeanRows 334).error 4 := by
  have he : (generalMeanRows 334).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 334) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 334)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0334

/-! Kernel-checked entropy margins for general spectral rectangle 335. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0335
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5055613834, 4881932942, 4716087125, 4557627726, 4406137791, 4261229305, 4122540724, 3989734767, 3862496432, 3740531217, 3623563503, 3511335104, 3403603944, 3300142858, 3200738500, 3105190345, 3013309783, 2924919278, 2839851611, 2757949170, 2679063313, 2603053764, 2529788071, 2459141096, 2390994545, 2325236538, 2261761203, 2200468306, 2141262902, 2084055015, 2028759337, 1975294950, 1923585064, 1873556778, 1825140851, 1778271491, 1732886158, 1688925377, 1646332569, 1605053886, 1565038060, 1526236258, 1488601955, 1452090801, 1416660509, 1382270742, 1348883007, 1316460563, 1284968321, 1254372767, 1224641870, 1195745015, 1167652922, 1140337584, 1113772201, 1087931116, 1062789764, 1038324610, 1014513104, 991333632, 968765468, 946788731, 925384345, 904534003, 884220126, 864425830, 845134895, 826331733, 808001356, 790129353, 772701859, 755705533, 739127534, 722955497, 707177513, 691782108, 676758222, 662095197, 647782752, 633810970, 620170283, 606851457, 593845576, 581144029, 568738500, 556620951, 544783616, 533218984, 521919792, 510879017, 500089861, 489545745, 479240302, 469167364, 459320960, 449695303, 440284786, 431083974, 422087599, 413290550, 404687872, 396274757, 388046540, 379998691, 372126815, 364426642, 356894027, 349524943, 342315475, 335261821, 328360285, 321607273, 314999291, 308532940, 302204916, 296012001, 289951066, 284019065, 278213035, 272530088, 266967415]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 335).prefactor = (4752614038175123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 335).cutoff/(generalMeanRows 335).c)).2 =
    (189175985601191/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 335).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 335).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 335).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 335

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 335).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 335).criticalRate j.val*(generalMeanRows 335).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 335).c*(generalMeanRows 335).criticalPoint j.val)).2-
      (generalMeanRows 335).J/2-(generalMeanRows 335).error (generalMeanGrid j.val)+
      (generalMeanRows 335).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 335).c)).2-
      (generalMeanRows 335).J/2-(generalMeanRows 335).error 4 := by
  have he : (generalMeanRows 335).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 335) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 335)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0335

/-! Kernel-checked entropy margins for general spectral rectangle 336. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0336
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5009826570, 4835432011, 4668902445, 4509789907, 4357677977, 4212179024, 4072931758, 3939599028, 3811865855, 3689437660, 3572038658, 3459410419, 3351310551, 3247511507, 3147799508, 3051973543, 2959844471, 2871234192, 2785974887, 2703908319, 2624885193, 2548764566, 2475413299, 2404705556, 2336522336, 2270751044, 2207285090, 2146023520, 2086870667, 2029735838, 1974533009, 1921180553, 1869600976, 1819720682, 1771469743, 1724781688, 1679593310, 1635844480, 1593477973, 1552439310, 1512676603, 1474140414, 1436783624, 1400561305, 1365430605, 1331350635, 1298282365, 1266188532, 1235033538, 1204783372, 1175405526, 1146868915, 1119143810, 1092201762, 1066015546, 1040559094, 1015807440, 991736666, 968323849, 945547012, 923385083, 901817844, 880825897, 860390621, 840494136, 821119269, 802249521, 783869035, 765962566, 748515454, 731513597, 714943425, 698791878, 683046381, 667694824, 652725538, 638127283, 623889220, 610000902, 596452251, 583233545, 570335404, 557748772, 545464906, 533475363, 521771985, 510346892, 499192465, 488301339, 477666394, 467280739, 457137711, 447230859, 437553940, 428100909, 418865913, 409843279, 401027516, 392413297, 383995462, 375769007, 367729080, 359870974, 352190122, 344682094, 337342590, 330167435, 323152575, 316294074, 309588109, 303030965, 296619032, 290348804, 284216870, 278219915, 272354716, 266618139, 261007134, 255518735, 250150055, 244898285]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 336).prefactor = (2377140471470981/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 336).cutoff/(generalMeanRows 336).c)).2 =
    (45576133951771/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 336).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 336).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 336).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 336

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 336).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 336).criticalRate j.val*(generalMeanRows 336).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 336).c*(generalMeanRows 336).criticalPoint j.val)).2-
      (generalMeanRows 336).J/2-(generalMeanRows 336).error (generalMeanGrid j.val)+
      (generalMeanRows 336).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 336).c)).2-
      (generalMeanRows 336).J/2-(generalMeanRows 336).error 4 := by
  have he : (generalMeanRows 336).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 336) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 336)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0336

/-! Kernel-checked entropy margins for general spectral rectangle 337. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0337
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4880656001, 4706093162, 4539465714, 4380322060, 4228242348, 4082835705, 3943737767, 3810608471, 3683130074, 3561005366, 3443956065, 3331721358, 3224056584, 3120732035, 3021531860, 2926253078, 2834704662, 2746706706, 2662089663, 2580693646, 2502367774, 2426969589, 2354364496, 2284425265, 2217031557, 2152069496, 2089431259, 2029014710, 1970723049, 1914464492, 1860151971, 1807702853, 1757038683, 1708084936, 1660770794, 1615028934, 1570795329, 1528009061, 1486612150, 1446549390, 1407768196, 1370218462, 1333852426, 1298624545, 1264491374, 1231411458, 1199345225, 1168254888, 1138104351, 1108859126, 1080486243, 1052954182, 1026232789, 1000293218, 975107858, 950650272, 926895145, 903818222, 881396260, 859606978, 838429011, 817841866, 797825879, 778362178, 759432645, 741019879, 723107167, 705678446, 688718279, 672211822, 656144800, 640503481, 625274649, 610445586, 596004043, 581938227, 568236774, 554888737, 541883562, 529211075, 516861465, 504825266, 493093347, 481656893, 470507398, 459636646, 449036702, 438699900, 428618834, 418786344, 409195508, 399839634, 390712249, 381807089, 373118095, 364639402, 356365331, 348290384, 340409237, 332716731, 325207869, 317877808, 310721853, 303735453, 296914195, 290253799, 283750112, 277399107, 271196874, 265139620, 259223661, 253445422, 247801429, 242288311, 236902791, 231641686, 226501903, 221480436, 216574363, 211780844, 207097116]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 337).prefactor = (478899535205457/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 337).cutoff/(generalMeanRows 337).c)).2 =
    (174552442539101/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 337).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 337).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 337).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 337

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 337).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 337).criticalRate j.val*(generalMeanRows 337).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 337).c*(generalMeanRows 337).criticalPoint j.val)).2-
      (generalMeanRows 337).J/2-(generalMeanRows 337).error (generalMeanGrid j.val)+
      (generalMeanRows 337).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 337).c)).2-
      (generalMeanRows 337).J/2-(generalMeanRows 337).error 4 := by
  have he : (generalMeanRows 337).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 337) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 337)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0337

/-! Kernel-checked entropy margins for general spectral rectangle 338. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0338
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5322544786, 5155617752, 4996040223, 4843389828, 4697274190, 4557328302, 4423212197, 4294608852, 4171222309, 4052775989, 3939011163, 3829685574, 3724572188, 3623458053, 3526143266, 3432440032, 3342171797, 3255172459, 3171285645, 3090364045, 3012268799, 2936868935, 2864040848, 2793667819, 2725639575, 2659851873, 2596206121, 2534609029, 2474972273, 2417212199, 2361249532, 2307009118, 2254419672, 2203413554, 2153926555, 2105897692, 2059269026, 2013985485, 1969994703, 1927246863, 1885694559, 1845292656, 1805998169, 1767770141, 1730569535, 1694359128, 1659103414, 1624768510, 1591322072, 1558733213, 1526972424, 1496011506, 1465823499, 1436382616, 1407664188, 1379644604, 1352301256, 1325612491, 1299557560, 1274116579, 1249270477, 1225000963, 1201290487, 1178122201, 1155479927, 1133348123, 1111711856, 1090556771, 1069869061, 1049635447, 1029843149, 1010479864, 991533744, 972993377, 954847763, 937086300, 919698762, 902675287, 886006356, 869682781, 853695689, 838036509, 822696958, 807669032, 792944990, 778517344, 764378850, 750522496, 736941495, 723629272, 710579458, 697785881, 685242560, 672943692, 660883652, 649056980, 637458380, 626082708, 614924971, 603980318, 593244038, 582711551, 572378405, 562240273, 552292945, 542532326, 532954431, 523555383, 514331407, 505278826, 496394060, 487673622, 479114114, 470712222, 462464720, 454368458, 446420368, 438617455, 430956798, 423435548, 416050922]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 338).prefactor = (906568420869499/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 338).cutoff/(generalMeanRows 338).c)).2 =
    (211598597142313/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 338).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 338).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 338).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 338

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 338).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 338).criticalRate j.val*(generalMeanRows 338).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 338).c*(generalMeanRows 338).criticalPoint j.val)).2-
      (generalMeanRows 338).J/2-(generalMeanRows 338).error (generalMeanGrid j.val)+
      (generalMeanRows 338).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 338).c)).2-
      (generalMeanRows 338).J/2-(generalMeanRows 338).error 4 := by
  have he : (generalMeanRows 338).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 338) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 338)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0338

/-! Kernel-checked entropy margins for general spectral rectangle 339. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0339
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5305456995, 5136429224, 4974865149, 4820336410, 4672445039, 4530820803, 4395118841, 4265017539, 4140216635, 4020435497, 3905411587, 3794899057, 3688667487, 3586500728, 3488195858, 3393562222, 3302420563, 3214602216, 3129948377, 3048309431, 2969544327, 2893520012, 2820110901, 2749198393, 2680670419, 2614421028, 2550350000, 2488362489, 2428368690, 2370283530, 2314026383, 2259520800, 2206694260, 2155477942, 2105806501, 2057617871, 2010853074, 1965456043, 1921373457, 1878554586, 1836951144, 1796517155, 1757208825, 1718984422, 1681804161, 1645630105, 1610426057, 1576157474, 1542791376, 1510296263, 1478642038, 1447799936, 1417742450, 1388443270, 1359877223, 1332020210, 1304849155, 1278341954, 1252477425, 1227235263, 1202595994, 1178540941, 1155052176, 1132112490, 1109705359, 1087814904, 1066425869, 1045523585, 1025093947, 1005123383, 985598835, 966507730, 947837959, 929577859, 911716188, 894242110, 877145176, 860415304, 844042767, 828018173, 812332456, 796976857, 781942912, 767222442, 752807536, 738690546, 724864070, 711320946, 698054240, 685057238, 672323436, 659846533, 647620420, 635639176, 623897059, 612388497, 601108085, 590050577, 579210881, 568584049, 558165277, 547949898, 537933375, 528111297, 518479377, 509033445, 499769443, 490683425, 481771548, 473030072, 464455357, 456043855, 447792113, 439696764, 431754530, 423962212, 416316696, 408814941, 401453984, 394230935, 387142974]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 339).prefactor = (919409555754079/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 339).cutoff/(generalMeanRows 339).c)).2 =
    (415197151617551/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 339).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 339).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 339).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 339

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 339).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 339).criticalRate j.val*(generalMeanRows 339).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 339).c*(generalMeanRows 339).criticalPoint j.val)).2-
      (generalMeanRows 339).J/2-(generalMeanRows 339).error (generalMeanGrid j.val)+
      (generalMeanRows 339).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 339).c)).2-
      (generalMeanRows 339).J/2-(generalMeanRows 339).error 4 := by
  have he : (generalMeanRows 339).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 339) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 339)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0339

/-! Kernel-checked entropy margins for general spectral rectangle 340. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0340
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4922783931, 4748887276, 4582896087, 4424358191, 4272853311, 4127990287, 3989404594, 3856756121, 3729727182, 3608020716, 3491358669, 3379480537, 3272142027, 3169113862, 3070180674, 2975140008, 2883801401, 2795985550, 2711523536, 2630256124, 2552033109, 2476712722, 2404161072, 2334251642, 2266864815, 2201887437, 2139212414, 2078738336, 2020369128, 1964013727, 1909585781, 1857003367, 1806188729, 1757068036, 1709571153, 1663631428, 1619185492, 1576173077, 1534536837, 1494222189, 1455177154, 1417352223, 1380700212, 1345176146, 1310737130, 1277342246, 1244952444, 1213530446, 1183040648, 1153449040, 1124723119, 1096831811, 1069745401, 1043435463, 1017874793, 993037351, 968898201, 945433457, 922620230, 900436581, 878861476, 857874738, 837457010, 817589714, 798255014, 779435781, 761115562, 743278546, 725909533, 708993912, 692517626, 676467155, 660829485, 645592089, 630742903, 616270310, 602163113, 588410523, 575002140, 561927934, 549178230, 536743694, 524615317, 512784403, 501242556, 489981663, 478993890, 468271664, 457807666, 447594819, 437626279, 427895427, 418395855, 409121366, 400065957, 391223819, 382589324, 374157021, 365921628, 357878028, 350021257, 342346506, 334849110, 327524544, 320368418, 313376474, 306544577, 299868715, 293344992, 286969624, 280738937, 274649361, 268697429, 262879769, 257193106, 251634255, 246200121, 240887692, 235694041, 230616319, 225651756]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 340).prefactor = (299171578293797/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 340).cutoff/(generalMeanRows 340).c)).2 =
    (181363326649651/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 340).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 340).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 340).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 340

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 340).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 340).criticalRate j.val*(generalMeanRows 340).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 340).c*(generalMeanRows 340).criticalPoint j.val)).2-
      (generalMeanRows 340).J/2-(generalMeanRows 340).error (generalMeanGrid j.val)+
      (generalMeanRows 340).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 340).c)).2-
      (generalMeanRows 340).J/2-(generalMeanRows 340).error 4 := by
  have he : (generalMeanRows 340).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 340) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 340)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0340

/-! Kernel-checked entropy margins for general spectral rectangle 341. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0341
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4795339682, 4621359018, 4455352537, 4296864423, 4145470962, 4000777745, 3862417169, 3730046210, 3603344410, 3482012080, 3365768667, 3254351284, 3147513374, 3045023496, 2946664220, 2852231122, 2761531859, 2674385328, 2590620894, 2510077676, 2432603896, 2358056276, 2286299483, 2217205618, 2150653739, 2086529421, 2024724354, 1965135960, 1907667045, 1852225473, 1798723863, 1747079304, 1697213093, 1649050491, 1602520491, 1557555607, 1514091669, 1472067639, 1431425436, 1392109769, 1354067985, 1317249924, 1281607782, 1247095986, 1213671074, 1181291582, 1149917936, 1119512358, 1090038768, 1061462697, 1033751205, 1006872802, 980797374, 955496113, 930941454, 907107010, 883967516, 861498771, 839677588, 818481744, 797889934, 777881725, 758437516, 739538500, 721166621, 703304545, 685935622, 669043857, 652613879, 636630910, 621080743, 605949711, 591224666, 576892956, 562942398, 549361265, 536138261, 523262501, 510723499, 498511145, 486615692, 475027739, 463738218, 452738378, 442019773, 431574252, 421393940, 411471234, 401798786, 392369498, 383176508, 374213181, 365473105, 356950073, 348638083, 340531327, 332624184, 324911211, 317387140, 310046867, 302885450, 295898099, 289080173, 282427174, 275934742, 269598648, 263414793, 257379200, 251488010, 245737479, 240123975, 234643971, 229294043, 224070868, 218971217, 213991955, 209130036, 204382502, 199746477, 195219167, 190797855]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 341).prefactor = (4821121582818683/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 341).cutoff/(generalMeanRows 341).c)).2 =
    (347341734459821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 341).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 341).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 341).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 341

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 341).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 341).criticalRate j.val*(generalMeanRows 341).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 341).c*(generalMeanRows 341).criticalPoint j.val)).2-
      (generalMeanRows 341).J/2-(generalMeanRows 341).error (generalMeanGrid j.val)+
      (generalMeanRows 341).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 341).c)).2-
      (generalMeanRows 341).J/2-(generalMeanRows 341).error 4 := by
  have he : (generalMeanRows 341).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 341) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 341)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0341

/-! Kernel-checked entropy margins for general spectral rectangle 342. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0342
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5287693129, 5121874193, 4963412307, 4811880559, 4666882526, 4528049609, 4395038656, 4267529839, 4145224735, 4027844612, 3915128871, 3806833644, 3702730518, 3602605378, 3506257349, 3413497837, 3324149650, 3238046189, 3155030713, 3074955657, 2997682014, 2923078755, 2851022303, 2781396041, 2714089860, 2648999745, 2586027381, 2525079797, 2466069032, 2408911825, 2353529325, 2299846826, 2247793513, 2197302234, 2148309276, 2100754170, 2054579496, 2009730707, 1966155965, 1923805986, 1882633892, 1842595079, 1803647087, 1765749482, 1728863743, 1692953157, 1657982721, 1623919048, 1590730281, 1558386010, 1526857196, 1496116096, 1466136199, 1436892157, 1408359729, 1380515717, 1353337922, 1326805084, 1300896839, 1275593674, 1250876881, 1226728520, 1203131382, 1180068947, 1157525356, 1135485379, 1113934379, 1092858291, 1072243586, 1052077255, 1032346778, 1013040102, 994145622, 975652157, 957548933, 939825564, 922472032, 905478674, 888836165, 872535500, 856567984, 840925218, 825599084, 810581732, 795865574, 781443267, 767307705, 753452009, 739869520, 726553784, 713498551, 700697759, 688145534, 675836177, 663764159, 651924115, 640310837, 628919267, 617744494, 606781744, 596026380, 585473893, 575119899, 564960135, 554990450, 545206810, 535605286, 526182051, 516933380, 507855647, 498945315, 490198939, 481613163, 473184713, 464910397, 456787102, 448811792, 440981502, 433293343, 425744492, 418332193]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 342).prefactor = (4562307452797047/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 342).cutoff/(generalMeanRows 342).c)).2 =
    (434893234047819/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 342).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 342).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 342).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 342

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 342).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 342).criticalRate j.val*(generalMeanRows 342).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 342).c*(generalMeanRows 342).criticalPoint j.val)).2-
      (generalMeanRows 342).J/2-(generalMeanRows 342).error (generalMeanGrid j.val)+
      (generalMeanRows 342).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 342).c)).2-
      (generalMeanRows 342).J/2-(generalMeanRows 342).error 4 := by
  have he : (generalMeanRows 342).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 342) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 342)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0342

/-! Kernel-checked entropy margins for general spectral rectangle 343. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0343
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5323812260, 5156860650, 4997316344, 4844749514, 4698761030, 4558979773, 4425060251, 4296680447, 4173539903, 4055357980, 3941872301, 3832837332, 3728023100, 3627214026, 3530207863, 3436814731, 3346856225, 3260164609, 3176582071, 3095960039, 3018158556, 2943045698, 2870497043, 2800395178, 2732629243, 2667094511, 2603691996, 2542328092, 2482914237, 2425366600, 2369605794, 2315556601, 2263147723, 2212311548, 2162983930, 2115103985, 2068613901, 2023458759, 1979586367, 1936947104, 1895493772, 1855181462, 1815967425, 1777810950, 1740673252, 1704517368, 1669308056, 1635011701, 1601596229, 1569031021, 1537286839, 1506335754, 1476151070, 1446707269, 1417979941, 1389945733, 1362582292, 1335868213, 1309782995, 1284306989, 1259421360, 1235108048, 1211349722, 1188129752, 1165432171, 1143241643, 1121543433, 1100323378, 1079567859, 1059263776, 1039398524, 1019959968, 1000936424, 982316634, 964089751, 946245317, 928773247, 911663811, 894907620, 878495608, 862419022, 846669404, 831238579, 816118648, 801301966, 786781143, 772549024, 758598683, 744923414, 731516722, 718372311, 705484080, 692846113, 680452673, 668298194, 656377273, 644684667, 633215284, 621964178, 610926544, 600097713, 589473144, 579048424, 568819260, 558781475, 548931005, 539263894, 529776291, 520464445, 511324703, 502353506, 493547386, 484902963, 476416939, 468086103, 459907320, 451877531, 443993755, 436253080, 428652664, 421189733]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 343).prefactor = (2296735812928113/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 343).cutoff/(generalMeanRows 343).c)).2 =
    (434893234047819/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 343).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 343).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 343).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 343

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 343).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 343).criticalRate j.val*(generalMeanRows 343).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 343).c*(generalMeanRows 343).criticalPoint j.val)).2-
      (generalMeanRows 343).J/2-(generalMeanRows 343).error (generalMeanGrid j.val)+
      (generalMeanRows 343).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 343).c)).2-
      (generalMeanRows 343).J/2-(generalMeanRows 343).error 4 := by
  have he : (generalMeanRows 343).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 343) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 343)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0343

/-! Kernel-checked entropy margins for general spectral rectangle 344. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0344
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4855699949, 4681755966, 4515767628, 4357278993, 4205866295, 4061135147, 3922718034, 3790272076, 3663477011, 3542033395, 3425660958, 3314097133, 3207095716, 3104425644, 3005869893, 2911224462, 2820297449, 2732908208, 2648886570, 2568072132, 2490313599, 2415468182, 2343401041, 2273984770, 2207098921, 2142629561, 2080468870, 2020514757, 1962670510, 1906844470, 1852949723, 1800903824, 1750628525, 1702049534, 1655096284, 1609701718, 1565802088, 1523336768, 1482248076, 1442481115, 1403983613, 1366705781, 1330600177, 1295621579, 1261726865, 1228874901, 1197026434, 1166143995, 1136191805, 1107135684, 1078942971, 1051582448, 1025024260, 999239851, 974201897, 949884245, 926261851, 903310731, 881007902, 859331341, 838259930, 817773419, 797852381, 778478171, 759632895, 741299368, 723461085, 706102187, 689207433, 672762169, 656752305, 641164285, 625985068, 611202097, 596803287, 582776998, 569112016, 555797536, 542823142, 530178795, 517854809, 505841845, 494130888, 482713238, 471580497, 460724555, 450137578, 439811997, 429740497, 419916010, 410331697, 400980949, 391857370, 382954773, 374267168, 365788761, 357513937, 349437262, 341553472, 333857464, 326344297, 319009179, 311847466, 304854653, 298026373, 291358389, 284846590, 278486987, 272275708, 266208995, 260283197, 254494772, 248840276, 243316366, 237919794, 232647402, 227496122, 222462971, 217545049, 212739536, 208043691]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 344).prefactor = (2409832865818903/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 344).cutoff/(generalMeanRows 344).c)).2 =
    (357967572336047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 344).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 344).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 344).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 344

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 344).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 344).criticalRate j.val*(generalMeanRows 344).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 344).c*(generalMeanRows 344).criticalPoint j.val)).2-
      (generalMeanRows 344).J/2-(generalMeanRows 344).error (generalMeanGrid j.val)+
      (generalMeanRows 344).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 344).c)).2-
      (generalMeanRows 344).J/2-(generalMeanRows 344).error 4 := by
  have he : (generalMeanRows 344).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 344) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 344)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0344

/-! Kernel-checked entropy margins for general spectral rectangle 345. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0345
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4872962207, 4698399844, 4531821410, 4372769340, 4220818362, 4075572687, 3936663495, 3803746684, 3676500857, 3554625503, 3437839356, 3325878916, 3218497103, 3115462034, 3016555913, 2921574012, 2830323749, 2742623835, 2658303496, 2577201758, 2499166789, 2424055293, 2351731950, 2282068901, 2214945269, 2150246717, 2087865042, 2027697789, 1969647903, 1913623398, 1859537053, 1807306128, 1756852097, 1708100406, 1660980235, 1615424289, 1571368594, 1528752307, 1487517543, 1447609209, 1408974846, 1371564489, 1335330528, 1300227579, 1266212368, 1233243613, 1201281923, 1170289696, 1140231024, 1111071607, 1082778668, 1055320876, 1028668273, 1002792199, 977665234, 953261131, 929554759, 906522046, 884139930, 862386307, 841239987, 820680645, 800688786, 781245700, 762333428, 743934725, 726033026, 708612416, 691657600, 675153872, 659087093, 643443657, 628210476, 613374951, 598924953, 584848800, 571135238, 557773424, 544752906, 532063607, 519695809, 507640138, 495887548, 484429308, 473256990, 462362454, 451737840, 441375551, 431268247, 421408832, 411790447, 402406457, 393250443, 384316196, 375597707, 367089158, 358784917, 350679529, 342767711, 335044344, 327504467, 320143273, 312956099, 305938427, 299085872, 292394183, 285859234, 279477023, 273243662, 267155381, 261208517, 255399513, 249724916, 244181368, 238765611, 233474475, 228304882, 223253838, 218318432, 213495836, 208783297]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 345).prefactor = (38694399094007/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 345).cutoff/(generalMeanRows 345).c)).2 =
    (357967572336047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 345).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 345).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 345).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 345

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 345).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 345).criticalRate j.val*(generalMeanRows 345).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 345).c*(generalMeanRows 345).criticalPoint j.val)).2-
      (generalMeanRows 345).J/2-(generalMeanRows 345).error (generalMeanGrid j.val)+
      (generalMeanRows 345).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 345).c)).2-
      (generalMeanRows 345).J/2-(generalMeanRows 345).error 4 := by
  have he : (generalMeanRows 345).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 345) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 345)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0345

/-! Kernel-checked entropy margins for general spectral rectangle 346. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0346
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4812527903, 4637923630, 4471322122, 4312265930, 4160329820, 4015117970, 3876261461, 3743416036, 3616260092, 3494492863, 3377832792, 3266016049, 3158795194, 3055937955, 2957226124, 2862454544, 2771430182, 2683971287, 2599906611, 2519074697, 2441323223, 2366508397, 2294494402, 2225152880, 2158362455, 2094008293, 2031981694, 1972179714, 1914504810, 1858864515, 1805171136, 1753341464, 1703296515, 1654961281, 1608264501, 1563138446, 1519518718, 1477344059, 1436556179, 1397099591, 1358921452, 1321971421, 1286201525, 1251566026, 1218021308, 1185525755, 1154039655, 1123525093, 1093945859, 1065267361, 1037456541, 1010481796, 984312904, 958920955, 934278283, 910358408, 887135974, 864586692, 842687294, 821415477, 800749858, 780669933, 761156029, 742189272, 723751541, 705825441, 688394262, 671441951, 654953081, 638912824, 623306920, 608121653, 593343828, 578960747, 564960186, 551330373, 538059973, 525138062, 512554116, 500297989, 488359898, 476730409, 465400422, 454361155, 443604131, 433121169, 422904367, 412946094, 403238977, 393775891, 384549950, 375554496, 366783092, 358229510, 349887727, 341751914, 333816429, 326075810, 318524770, 311158187, 303971100, 296958704, 290116340, 283439494, 276923791, 270564987, 264358967, 258301740, 252389433, 246618291, 240984666, 235485019, 230115915, 224874018, 219756088, 214758979, 209879634, 205115083, 200462441, 195918903, 191481743]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 346).prefactor = (4838402215830117/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 346).cutoff/(generalMeanRows 346).c)).2 =
    (347341734459821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 346).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 346).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 346).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 346

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 346).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 346).criticalRate j.val*(generalMeanRows 346).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 346).c*(generalMeanRows 346).criticalPoint j.val)).2-
      (generalMeanRows 346).J/2-(generalMeanRows 346).error (generalMeanGrid j.val)+
      (generalMeanRows 346).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 346).c)).2-
      (generalMeanRows 346).J/2-(generalMeanRows 346).error 4 := by
  have he : (generalMeanRows 346).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 346) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 346)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0346

/-! Kernel-checked entropy margins for general spectral rectangle 347. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0347
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5287128864, 5121364210, 4962981937, 4811551560, 4666673427, 4527976031, 4395113598, 4267763940, 4145626517, 4028420695, 3915884175, 3807771571, 3703853114, 3603913488, 3507750753, 3415175375, 3326009335, 3240085312, 3157245935, 3077343099, 3000237328, 2925797199, 2853898803, 2784425246, 2717266200, 2652317470, 2589480609, 2528662549, 2469775266, 2412735466, 2357464294, 2303887061, 2251932992, 2201534992, 2152629426, 2105155910, 2059057127, 2014278642, 1970768739, 1928478261, 1887360466, 1847370892, 1808467223, 1770609172, 1733758370, 1697878254, 1662933976, 1628892302, 1595721528, 1563391396, 1531873017, 1501138801, 1471162383, 1441918561, 1413383235, 1385533351, 1358346846, 1331802594, 1305880365, 1280560772, 1255825233, 1231655931, 1208035773, 1184948355, 1162377930, 1140309374, 1118728156, 1097620310, 1076972407, 1056771530, 1037005250, 1017661602, 998729064, 980196538, 962053326, 944289116, 926893963, 909858273, 893172784, 876828558, 860816958, 845129643, 829758549, 814695881, 799934099, 785465908, 771284248, 757382284, 743753396, 730391172, 717289396, 704442044, 691843273, 679487417, 667368977, 655482615, 643823151, 632385551, 621164928, 610156531, 599355742, 588758073, 578359158, 568154750, 558140717, 548313037, 538667795, 529201178, 519909473, 510789064, 501836424, 493048119, 484420799, 475951200, 467636135, 459472499, 451457260, 443587460, 435860213, 428272700, 420822169]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 347).prefactor = (918303164014133/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 347).cutoff/(generalMeanRows 347).c)).2 =
    (440792956175007/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 347).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 347).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 347).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 347

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 347).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 347).criticalRate j.val*(generalMeanRows 347).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 347).c*(generalMeanRows 347).criticalPoint j.val)).2-
      (generalMeanRows 347).J/2-(generalMeanRows 347).error (generalMeanGrid j.val)+
      (generalMeanRows 347).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 347).c)).2-
      (generalMeanRows 347).J/2-(generalMeanRows 347).error 4 := by
  have he : (generalMeanRows 347).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 347) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 347)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0347

/-! Kernel-checked entropy margins for general spectral rectangle 348. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0348
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4809341866, 4634758080, 4468192333, 4309185228, 4157309766, 4012168522, 3873391127, 3740632015, 3613568396, 3491898437, 3375339616, 3263627238, 3156513082, 3053764182, 2955161703, 2860499932, 2769585342, 2682235742, 2598279497, 2517554809, 2439909057, 2365198190, 2293286166, 2224044435, 2157351456, 2093092259, 2031158032, 1971445737, 1913857761, 1858301582, 1804689467, 1752938183, 1702968735, 1654706114, 1608079069, 1563019890, 1519464203, 1477350787, 1436621390, 1397220569, 1359095531, 1322195991, 1286474029, 1251883971, 1218382258, 1185927342, 1154479575, 1124001106, 1094455796, 1065809118, 1038028082, 1011081154, 984938178, 959570312, 934949956, 911050697, 887847241, 865315366, 843431864, 822174494, 801521935, 781453739, 761950295, 742992780, 724563132, 706644007, 689218746, 672271349, 655786437, 639749227, 624145507, 608961605, 594184369, 579801142, 565799740, 552168430, 538895913, 525971302, 513384107, 501124216, 489181876, 477547686, 466212574, 455167785, 444404872, 433915678, 423692325, 413727208, 404012974, 394542522, 385308985, 376305727, 367526327, 358964577, 350614470, 342470194, 334526123, 326776808, 319216977, 311841522, 304645494, 297624098, 290772689, 284086764, 277561955, 271194030, 264978882, 258912529, 252991107, 247210866, 241568166, 236059477, 230681367, 225430507, 220303662, 215297692, 210409544, 205636253, 200974937, 196422796, 191977107]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 348).prefactor = (4853994954650803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 348).cutoff/(generalMeanRows 348).c)).2 =
    (175152349795239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 348).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 348).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 348).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 348

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 348).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 348).criticalRate j.val*(generalMeanRows 348).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 348).c*(generalMeanRows 348).criticalPoint j.val)).2-
      (generalMeanRows 348).J/2-(generalMeanRows 348).error (generalMeanGrid j.val)+
      (generalMeanRows 348).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 348).c)).2-
      (generalMeanRows 348).J/2-(generalMeanRows 348).error 4 := by
  have he : (generalMeanRows 348).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 348) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 348)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0348

/-! Kernel-checked entropy margins for general spectral rectangle 349. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0349
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4880044749, 4705187179, 4538335098, 4379029164, 4226842475, 4081377747, 3942264788, 3809158237, 3681735542, 3559695131, 3442754766, 3330650054, 3223133092, 3119971245, 3020946025, 2925852070, 2834496214, 2746696634, 2662282065, 2581091083, 2502971443, 2427779470, 2355379498, 2285643349, 2218449855, 2153684415, 2091238579, 2031009670, 1972900430, 1916818685, 1862677046, 1810392616, 1759886729, 1711084700, 1663915594, 1618312008, 1574209871, 1531548252, 1490269186, 1450317506, 1411640690, 1374188713, 1337913910, 1302770849, 1268716212, 1235708679, 1203708824, 1172679011, 1142583306, 1113387382, 1085058440, 1057565129, 1030877472, 1004966795, 979805663, 955367815, 931628110, 908562467, 886147815, 864362042, 843183952, 822593214, 802570328, 783096579, 764154006, 745725358, 727794070, 710344223, 693360520, 676828253, 660733281, 645061998, 629801313, 614938626, 600461807, 586359173, 572619469, 559231851, 546185865, 533471435, 521078840, 508998705, 497221983, 485739943, 474544154, 463626477, 452979047, 442594269, 432464799, 422583541, 412943632, 403538437, 394361536, 385406716, 376667966, 368139467, 359815584, 351690860, 343760010, 336017911, 328459601, 321080270, 313875252, 306840027, 299970207, 293261538, 286709892, 280311261, 274061758, 267957608, 261995145, 256170810, 250481145, 244922792, 239492486, 234187057, 229003422, 223938584, 218989630, 214153728, 209428121]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 349).prefactor = (4853112585829407/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 349).cutoff/(generalMeanRows 349).c)).2 =
    (359452353603627/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 349).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 349).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 349).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 349

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 349).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 349).criticalRate j.val*(generalMeanRows 349).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 349).c*(generalMeanRows 349).criticalPoint j.val)).2-
      (generalMeanRows 349).J/2-(generalMeanRows 349).error (generalMeanGrid j.val)+
      (generalMeanRows 349).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 349).c)).2-
      (generalMeanRows 349).J/2-(generalMeanRows 349).error 4 := by
  have he : (generalMeanRows 349).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 349) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 349)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0349

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock04 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 4 i) := by
  fin_cases i
  · exact EntropyRow0280.numerical
  · exact EntropyRow0281.numerical
  · exact EntropyRow0282.numerical
  · exact EntropyRow0283.numerical
  · exact EntropyRow0284.numerical
  · exact EntropyRow0285.numerical
  · exact EntropyRow0286.numerical
  · exact EntropyRow0287.numerical
  · exact EntropyRow0288.numerical
  · exact EntropyRow0289.numerical
  · exact EntropyRow0290.numerical
  · exact EntropyRow0291.numerical
  · exact EntropyRow0292.numerical
  · exact EntropyRow0293.numerical
  · exact EntropyRow0294.numerical
  · exact EntropyRow0295.numerical
  · exact EntropyRow0296.numerical
  · exact EntropyRow0297.numerical
  · exact EntropyRow0298.numerical
  · exact EntropyRow0299.numerical
  · exact EntropyRow0300.numerical
  · exact EntropyRow0301.numerical
  · exact EntropyRow0302.numerical
  · exact EntropyRow0303.numerical
  · exact EntropyRow0304.numerical
  · exact EntropyRow0305.numerical
  · exact EntropyRow0306.numerical
  · exact EntropyRow0307.numerical
  · exact EntropyRow0308.numerical
  · exact EntropyRow0309.numerical
  · exact EntropyRow0310.numerical
  · exact EntropyRow0311.numerical
  · exact EntropyRow0312.numerical
  · exact EntropyRow0313.numerical
  · exact EntropyRow0314.numerical
  · exact EntropyRow0315.numerical
  · exact EntropyRow0316.numerical
  · exact EntropyRow0317.numerical
  · exact EntropyRow0318.numerical
  · exact EntropyRow0319.numerical
  · exact EntropyRow0320.numerical
  · exact EntropyRow0321.numerical
  · exact EntropyRow0322.numerical
  · exact EntropyRow0323.numerical
  · exact EntropyRow0324.numerical
  · exact EntropyRow0325.numerical
  · exact EntropyRow0326.numerical
  · exact EntropyRow0327.numerical
  · exact EntropyRow0328.numerical
  · exact EntropyRow0329.numerical
  · exact EntropyRow0330.numerical
  · exact EntropyRow0331.numerical
  · exact EntropyRow0332.numerical
  · exact EntropyRow0333.numerical
  · exact EntropyRow0334.numerical
  · exact EntropyRow0335.numerical
  · exact EntropyRow0336.numerical
  · exact EntropyRow0337.numerical
  · exact EntropyRow0338.numerical
  · exact EntropyRow0339.numerical
  · exact EntropyRow0340.numerical
  · exact EntropyRow0341.numerical
  · exact EntropyRow0342.numerical
  · exact EntropyRow0343.numerical
  · exact EntropyRow0344.numerical
  · exact EntropyRow0345.numerical
  · exact EntropyRow0346.numerical
  · exact EntropyRow0347.numerical
  · exact EntropyRow0348.numerical
  · exact EntropyRow0349.numerical
end SingularValueBounds.KL.Certificates
