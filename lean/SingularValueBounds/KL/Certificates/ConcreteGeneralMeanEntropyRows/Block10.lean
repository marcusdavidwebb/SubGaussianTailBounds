import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 700. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0700
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4967463919, 4796930542, 4633937862, 4478062559, 4328910951, 4186116410, 4049337056, 3918253689, 3792567945, 3672000623, 3556290187, 3445191408, 3338474132, 3235922162, 3137332242, 3042513126, 2951284734, 2863477372, 2778931023, 2697494692, 2619025805, 2543389657, 2470458898, 2400113063, 2332238138, 2266726151, 2203474803, 2142387115, 2083371112, 2026339516, 1971209473, 1917902287, 1866343182, 1816461073, 1768188359, 1721460717, 1676216926, 1632398691, 1589950478, 1548819366, 1508954906, 1470308982, 1432835691, 1396491221, 1361233745, 1327023312, 1293821754, 1261592590, 1230300940, 1199913444, 1170398187, 1141724621, 1113863502, 1086786822, 1060467747, 1034880565, 1010000624, 985804286, 962268876, 939372635, 917094680, 895414959, 874314213, 853773941, 833776361, 814304381, 795341564, 776872102, 758880782, 741352966, 724274560, 707631993, 691412190, 675602556, 660190950, 645165670, 630515429, 616229341, 602296903, 588707978, 575452781, 562521863, 549906099, 537596673, 525585065, 513863040, 502422637, 491256159, 480356158, 469715429, 459327000, 449184124, 439280265, 429609097, 420164491, 410940510, 401931400, 393131584, 384535658, 376138378, 367934661, 359919577, 352088339, 344436306, 336958972, 329651961, 322511026, 315532042, 308711003, 302044016, 295527300, 289157179, 282930081, 276842533, 270891159, 265072674, 259383887, 253821690, 248383061, 243065059, 237864823]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 700).prefactor = (2325016812613957/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 700).cutoff/(generalMeanRows 700).c)).2 =
    (7063144045663/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 700).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 700).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 700).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 700

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 700).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 700).criticalRate j.val*(generalMeanRows 700).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 700).c*(generalMeanRows 700).criticalPoint j.val)).2-
      (generalMeanRows 700).J/2-(generalMeanRows 700).error (generalMeanGrid j.val)+
      (generalMeanRows 700).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 700).c)).2-
      (generalMeanRows 700).J/2-(generalMeanRows 700).error 4 := by
  have he : (generalMeanRows 700).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 700) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 700)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0700

/-! Kernel-checked entropy margins for general spectral rectangle 701. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0701
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5321682996, 5154893043, 4995339930, 4842612426, 4696328394, 4556132253, 4421692705, 4292700708, 4168867650, 4049923710, 3935616381, 3825709132, 3719980192, 3618221452, 3520237459, 3425844506, 3334869789, 3247150649, 3162533867, 3080875020, 3002037888, 2925893911, 2852321683, 2781206489, 2712439876, 2645919252, 2581547521, 2519232741, 2458887805, 2400430146, 2343781466, 2288867477, 2235617664, 2183965063, 2133846055, 2085200172, 2037969915, 1992100586, 1947540130, 1904238986, 1862149949, 1821228038, 1781430379, 1742716081, 1705046140, 1668383329, 1632692106, 1597938525, 1564090152, 1531115987, 1498986386, 1467672993, 1437148676, 1407387460, 1378364473, 1350055887, 1322438868, 1295491524, 1269192863, 1243522744, 1218461837, 1193991585, 1170094166, 1146752457, 1123950003, 1101670980, 1079900174, 1058622945, 1037825202, 1017493381, 997614419, 978175727, 959165178, 940571076, 922382143, 904587500, 887176648, 870139451, 853466121, 837147204, 821173565, 805536373, 790227090, 775237459, 760559489, 746185450, 732107856, 718319459, 704813238, 691582390, 678620323, 665920645, 653477156, 641283844, 629334876, 617624589, 606147487, 594898232, 583871639, 573062672, 562466436, 552078174, 541893259, 531907194, 522115602, 512514227, 503098926, 493865665, 484810520, 475929666, 467219381, 458676037, 450296099, 442076124, 434012752, 426102712, 418342810, 410729934, 403261047, 395933186, 388743460]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 701).prefactor = (4541776302932597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 701).cutoff/(generalMeanRows 701).c)).2 =
    (205105195865993/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 701).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 701).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 701).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 701

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 701).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 701).criticalRate j.val*(generalMeanRows 701).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 701).c*(generalMeanRows 701).criticalPoint j.val)).2-
      (generalMeanRows 701).J/2-(generalMeanRows 701).error (generalMeanGrid j.val)+
      (generalMeanRows 701).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 701).c)).2-
      (generalMeanRows 701).J/2-(generalMeanRows 701).error 4 := by
  have he : (generalMeanRows 701).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 701) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 701)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0701

/-! Kernel-checked entropy margins for general spectral rectangle 702. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0702
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4883398541, 4713380662, 4550939055, 4395646753, 4247106727, 4104949277, 3968829700, 3838426209, 3713438062, 3593583876, 3478600115, 3368239715, 3262270837, 3160475741, 3062649756, 2968600341, 2878146229, 2791116641, 2707350565, 2626696100, 2549009843, 2474156330, 2402007521, 2332442325, 2265346152, 2200610512, 2138132631, 2077815105, 2019565567, 1963296392, 1908924407, 1856370631, 1805560034, 1756421302, 1708886626, 1662891503, 1618374549, 1575277327, 1533544177, 1493122069, 1453960458, 1416011147, 1379228162, 1343567635, 1308987689, 1275448336, 1242911376, 1211340305, 1180700229, 1150957779, 1122081036, 1094039455, 1066803799, 1040346070, 1014639451, 989658249, 965377833, 941774591, 918825876, 896509960, 874805991, 853693952, 833154620, 813169530, 793720942, 774791801, 756365714, 738426913, 720960229, 703951067, 687385378, 671249634, 655530808, 640216348, 625294162, 610752591, 596580397, 582766739, 569301160, 556173572, 543374236, 530893749, 518723034, 506853320, 495276135, 483983292, 472966875, 462219233, 451732965, 441500913, 431516151, 421771975, 412261898, 402979639, 393919113, 385074430, 376439879, 368009930, 359779222, 351742556, 343894894, 336231348, 328747178, 321437783, 314298702, 307325603, 300514282, 293860655, 287360760, 281010747, 274806874, 268745510, 262823123, 257036282, 251381653, 245855991, 240456146, 235179050, 230021723, 224981263, 220054848]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 702).prefactor = (467701507936771/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 702).cutoff/(generalMeanRows 702).c)).2 =
    (175714472425497/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 702).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 702).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 702).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 702

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 702).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 702).criticalRate j.val*(generalMeanRows 702).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 702).c*(generalMeanRows 702).criticalPoint j.val)).2-
      (generalMeanRows 702).J/2-(generalMeanRows 702).error (generalMeanGrid j.val)+
      (generalMeanRows 702).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 702).c)).2-
      (generalMeanRows 702).J/2-(generalMeanRows 702).error 4 := by
  have he : (generalMeanRows 702).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 702) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 702)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0702

/-! Kernel-checked entropy margins for general spectral rectangle 703. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0703
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5024679330, 4854294101, 4691454743, 4535734665, 4386737284, 4244093399, 4107458866, 3976512497, 3850954188, 3730503234, 3614896803, 3503888560, 3397247418, 3294756405, 3196211632, 3101421352, 3010205098, 2922392895, 2837824543, 2756348947, 2677823512, 2602113578, 2529091905, 2458638192, 2390638636, 2324985521, 2261576839, 2200315939, 2141111200, 2083875722, 2028527052, 1974986912, 1923180958, 1873038550, 1824492539, 1777479065, 1731937372, 1687809633, 1645040787, 1603578383, 1563372440, 1524375310, 1486541551, 1449827813, 1414192719, 1379596766, 1346002224, 1313373045, 1281674772, 1250874464, 1220940608, 1191843057, 1163552952, 1136042666, 1109285733, 1083256798, 1057931559, 1033286718, 1009299925, 985949744, 963215597, 941077731, 919517176, 898515710, 878055821, 858120674, 838694085, 819760485, 801304894, 783312895, 765770608, 748664668, 731982198, 715710790, 699838486, 684353753, 669245472, 654502913, 640115725, 626073912, 612367827, 598988151, 585925881, 573172317, 560719051, 548557954, 536681163, 525081073, 513750326, 502681799, 491868599, 481304049, 470981684, 460895241, 451038650, 441406029, 431991676, 422790060, 413795819, 405003752, 396408809, 388006094, 379790850, 371758461, 363904445, 356224447, 348714237, 341369706, 334186860, 327161815, 320290799, 313570141, 306996273, 300565724, 294275115, 288121162, 282100666, 276210515, 270447680, 264809211, 259292236]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 703).prefactor = (1168412503616547/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 703).cutoff/(generalMeanRows 703).c)).2 =
    (368878426258927/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 703).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 703).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 703).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 703

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 703).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 703).criticalRate j.val*(generalMeanRows 703).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 703).c*(generalMeanRows 703).criticalPoint j.val)).2-
      (generalMeanRows 703).J/2-(generalMeanRows 703).error (generalMeanGrid j.val)+
      (generalMeanRows 703).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 703).c)).2-
      (generalMeanRows 703).J/2-(generalMeanRows 703).error 4 := by
  have he : (generalMeanRows 703).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 703) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 703)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0703

/-! Kernel-checked entropy margins for general spectral rectangle 704. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0704
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4960713887, 4790207428, 4627282071, 4471509472, 4322491386, 4179857044, 4043260808, 3912380076, 3786913398, 3666578789, 3551112194, 3440266116, 3333808357, 3231520885, 3133198795, 3038649372, 2947691218, 2860153472, 2775875079, 2694704130, 2616497245, 2541119013, 2468441475, 2398343635, 2330711027, 2265435295, 2202413820, 2141549360, 2082749726, 2025927477, 1970999633, 1917887415, 1866515995, 1816814267, 1768714634, 1722152807, 1677067616, 1633400838, 1591097026, 1550103365, 1510369518, 1471847499, 1434491541, 1398257977, 1363105130, 1328993209, 1295884206, 1263741804, 1232531293, 1202219482, 1172774626, 1144166350, 1116365580, 1089344478, 1063076382, 1037535744, 1012698081, 988539918, 965038741, 942172951, 919921819, 898265447, 877184724, 856661296, 836677523, 817216452, 798261782, 779797835, 761809528, 744282345, 727202313, 710555977, 694330377, 678513026, 663091889, 648055365, 633392266, 619091802, 605143559, 591537491, 578263896, 565313407, 552676977, 540345865, 528311624, 516566088, 505101364, 493909815, 482984057, 472316942, 461901554, 451731198, 441799391, 432099854, 422626504, 413373449, 404334976, 395505548, 386879799, 378452521, 370218666, 362173334, 354311771, 346629365, 339121636, 331784235, 324612939, 317603647, 310752374, 304055248, 297508507, 291108493, 284851650, 278734523, 272753749, 266906058, 261188271, 255597293, 250130112, 244783798, 239555499]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 704).prefactor = (1172541045588821/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 704).cutoff/(generalMeanRows 704).c)).2 =
    (90381362988417/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 704).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 704).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 704).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 704

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 704).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 704).criticalRate j.val*(generalMeanRows 704).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 704).c*(generalMeanRows 704).criticalPoint j.val)).2-
      (generalMeanRows 704).J/2-(generalMeanRows 704).error (generalMeanGrid j.val)+
      (generalMeanRows 704).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 704).c)).2-
      (generalMeanRows 704).J/2-(generalMeanRows 704).error 4 := by
  have he : (generalMeanRows 704).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 704) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 704)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0704

/-! Kernel-checked entropy margins for general spectral rectangle 705. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0705
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4980910815, 4809774529, 4646233482, 4489859456, 4340254288, 4197047249, 4059892704, 3928468014, 3802471667, 3681621581, 3565653584, 3454320035, 3347388573, 3244640983, 3145872165, 3050889191, 2959510440, 2871564818, 2786891027, 2705336907, 2626758824, 2551021107, 2477995529, 2407560830, 2339602275, 2274011240, 2210684833, 2149525546, 2090440922, 2033343254, 1978149297, 1924780012, 1873160313, 1823218840, 1774887746, 1728102494, 1682801672, 1638926818, 1596422254, 1555234934, 1515314299, 1476612143, 1439082484, 1402681449, 1367367155, 1333099613, 1299840620, 1267553672, 1236203875, 1205757860, 1176183708, 1147450874, 1119530121, 1092393453, 1066014051, 1040366221, 1015425333, 991167770, 967570884, 944612942, 922273088, 900531300, 879368349, 858765763, 838705791, 819171371, 800146099, 781614194, 763560477, 745970337, 728829709, 712125052, 695843320, 679971944, 664498810, 649412242, 634700978, 620354156, 606361296, 592712283, 579397354, 566407081, 553732357, 541364385, 529294663, 517514973, 506017371, 494794170, 483837941, 473141490, 462697857, 452500306, 442542313, 432817560, 423319929, 414043489, 404982494, 396131375, 387484732, 379037328, 370784083, 362720072, 354840512, 347140764, 339616324, 332262819, 325076002, 318051749, 311186055, 304475026, 297914880, 291501941, 285232635, 279103488, 273111120, 267252247, 261523671, 255922284, 250445060, 245089054, 239851401]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 705).prefactor = (938736304825981/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 705).cutoff/(generalMeanRows 705).c)).2 =
    (358728247332607/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 705).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 705).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 705).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 705

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 705).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 705).criticalRate j.val*(generalMeanRows 705).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 705).c*(generalMeanRows 705).criticalPoint j.val)).2-
      (generalMeanRows 705).J/2-(generalMeanRows 705).error (generalMeanGrid j.val)+
      (generalMeanRows 705).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 705).c)).2-
      (generalMeanRows 705).J/2-(generalMeanRows 705).error 4 := by
  have he : (generalMeanRows 705).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 705) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 705)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0705

/-! Kernel-checked entropy margins for general spectral rectangle 706. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0706
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4918264328, 4747032579, 4583431196, 4427030160, 4277429610, 4134257204, 3997165780, 3865831253, 3739950733, 3619240829, 3503436124, 3392287789, 3285562329, 3183040451, 3084516022, 2989795127, 2898695204, 2811044254, 2726680118, 2645449808, 2567208897, 2491820955, 2419157029, 2349095161, 2281519945, 2216322114, 2153398163, 2092649990, 2033984571, 1977313653, 1922553471, 1869624480, 1818451112, 1768961546, 1721087489, 1674763976, 1629929187, 1586524266, 1544493155, 1503782448, 1464341236, 1426120980, 1389075377, 1353160246, 1318333411, 1284554599, 1251785336, 1219988858, 1189130023, 1159175222, 1130092309, 1101850521, 1074420411, 1047773783, 1021883628, 996724068, 972270299, 948498538, 925385977, 902910733, 881051805, 859789033, 839103057, 818975281, 799387836, 780323548, 761765905, 743699027, 726107637, 708977036, 692293073, 676042126, 660211072, 644787273, 629758547, 615113155, 600839776, 586927493, 573365775, 560144460, 547253741, 534684148, 522426538, 510472078, 498812237, 487438766, 476343696, 465519320, 454958183, 444653078, 434597028, 424783282, 415205307, 405856775, 396731560, 387823729, 379127531, 370637395, 362347922, 354253877, 346350186, 338631924, 331094319, 323732739, 316542687, 309519803, 302659850, 295958720, 289412417, 283017067, 276768901, 270664260, 264699590, 258871433, 253176431, 247611319, 242172920, 236858148, 231663999, 226587552, 221625964]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 706).prefactor = (471040735941711/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 706).cutoff/(generalMeanRows 706).c)).2 =
    (175714472425497/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 706).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 706).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 706).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 706

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 706).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 706).criticalRate j.val*(generalMeanRows 706).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 706).c*(generalMeanRows 706).criticalPoint j.val)).2-
      (generalMeanRows 706).J/2-(generalMeanRows 706).error (generalMeanGrid j.val)+
      (generalMeanRows 706).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 706).c)).2-
      (generalMeanRows 706).J/2-(generalMeanRows 706).error 4 := by
  have he : (generalMeanRows 706).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 706) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 706)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0706

/-! Kernel-checked entropy margins for general spectral rectangle 707. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0707
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5183298886, 5015955615, 4855921477, 4702782084, 4556152307, 4415673728, 4281012351, 4151856562, 4027915304, 3908916419, 3794605169, 3684742886, 3579105756, 3477483711, 3379679420, 3285507371, 3194793028, 3107372067, 3023089665, 2941799857, 2863364940, 2787654922, 2714547017, 2643925181, 2575679676, 2509706672, 2445907878, 2384190196, 2324465405, 2266649860, 2210664222, 2156433196, 2103885294, 2052952611, 2003570620, 1955677972, 1909216317, 1864130134, 1820366573, 1777875303, 1736608373, 1696520084, 1657566861, 1619707144, 1582901274, 1547111393, 1512301350, 1478436610, 1445484168, 1413412471, 1382191343, 1351791913, 1322186550, 1293348798, 1265253320, 1237875837, 1211193082, 1185182745, 1159823426, 1135094594, 1110976543, 1087450352, 1064497846, 1042101564, 1020244724, 998911190, 978085440, 957752544, 937898130, 918508363, 899569917, 881069955, 862996106, 845336444, 828079468, 811214085, 794729589, 778615648, 762862286, 747459866, 732399080, 717670931, 703266723, 689178045, 675396763, 661915007, 648725160, 635819847, 623191927, 610834485, 598740817, 586904430, 575319027, 563978504, 552876939, 542008586, 531367873, 520949388, 510747878, 500758242, 490975525, 481394913, 472011727, 462821421, 453819575, 445001890, 436364185, 427902392, 419612556, 411490823, 403533447, 395736776, 388097257, 380611430, 373275921, 366087445, 359042803, 352138874, 345372616, 338741065, 332241329]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 707).prefactor = (182942774121029/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 707).cutoff/(generalMeanRows 707).c)).2 =
    (197586257183723/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 707).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 707).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 707).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 707

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 707).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 707).criticalRate j.val*(generalMeanRows 707).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 707).c*(generalMeanRows 707).criticalPoint j.val)).2-
      (generalMeanRows 707).J/2-(generalMeanRows 707).error (generalMeanGrid j.val)+
      (generalMeanRows 707).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 707).c)).2-
      (generalMeanRows 707).J/2-(generalMeanRows 707).error 4 := by
  have he : (generalMeanRows 707).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 707) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 707)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0707

/-! Kernel-checked entropy margins for general spectral rectangle 708. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0708
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5133958328, 4965806371, 4805024988, 4651196707, 4503933509, 4362874253, 4227682382, 4098043868, 3973665370, 3854272577, 3739608708, 3629433162, 3523520292, 3421658288, 3323648164, 3229302833, 3138446264, 3050912703, 2966545969, 2885198798, 2806732248, 2731015142, 2657923566, 2587340391, 2519154847, 2453262112, 2389562947, 2327963346, 2268374214, 2210711075, 2154893785, 2100846282, 2048496340, 1997775348, 1948618096, 1900962583, 1854749831, 1809923717, 1766430810, 1724220222, 1683243468, 1643454332, 1604808745, 1567264668, 1530781986, 1495322399, 1460849332, 1427327842, 1394724531, 1363007468, 1332146114, 1302111248, 1272874901, 1244410295, 1216691780, 1189694778, 1163395732, 1137772056, 1112802082, 1088465024, 1064740927, 1041610633, 1019055740, 997058566, 975602119, 954670058, 934246670, 914316835, 894866002, 875880163, 857345827, 839249999, 821580153, 804324218, 787470553, 771007930, 754925514, 739212850, 723859843, 708856745, 694194138, 679862922, 665854301, 652159772, 638771109, 625680357, 612879815, 600362033, 588119795, 576146112, 564434218, 552977552, 541769758, 530804674, 520076323, 509578911, 499306814, 489254574, 479416898, 469788641, 460364811, 451140559, 442111174, 433272076, 424618817, 416147071, 407852632, 399731411, 391779429, 383992815, 376367803, 368900729, 361588022, 354426211, 347411911, 340541828, 333812752, 327221557, 320765196, 314440700, 308245173]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 708).prefactor = (4605584958781397/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 708).cutoff/(generalMeanRows 708).c)).2 =
    (387737535879929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 708).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 708).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 708).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 708

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 708).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 708).criticalRate j.val*(generalMeanRows 708).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 708).c*(generalMeanRows 708).criticalPoint j.val)).2-
      (generalMeanRows 708).J/2-(generalMeanRows 708).error (generalMeanGrid j.val)+
      (generalMeanRows 708).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 708).c)).2-
      (generalMeanRows 708).J/2-(generalMeanRows 708).error 4 := by
  have he : (generalMeanRows 708).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 708) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 708)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0708

/-! Kernel-checked entropy margins for general spectral rectangle 709. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0709
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5163636034, 4995686439, 4835146067, 4681591275, 4534628461, 4393891437, 4259039090, 4129753285, 4005736986, 3886712558, 3772420242, 3662616773, 3557074124, 3455578370, 3357928652, 3263936226, 3173423606, 3086223766, 3002179421, 2921142354, 2842972811, 2767538930, 2694716224, 2624387101, 2556440417, 2490771069, 2427279610, 2365871898, 2306458770, 2248955731, 2193282678, 2139363632, 2087126491, 2036502807, 1987427563, 1939838982, 1893678335, 1848889770, 1805420146, 1763218880, 1722237808, 1682431047, 1643754869, 1606167587, 1569629440, 1534102491, 1499550528, 1465938974, 1433234798, 1401406438, 1370423717, 1340257781, 1310881022, 1282267018, 1254390473, 1227227161, 1200753868, 1174948345, 1149789261, 1125256156, 1101329395, 1077990136, 1055220285, 1033002461, 1011319966, 990156747, 969497370, 949326989, 929631319, 910396610, 891609623, 873257607, 855328275, 837809785, 820690720, 803960068, 787607205, 771621879, 755994191, 740714582, 725773820, 711162982, 696873443, 682896865, 669225183, 655850594, 642765547, 629962732, 617435073, 605175712, 593178010, 581435527, 569942027, 558691457, 547677951, 536895815, 526339526, 516003722, 505883197, 495972897, 486267911, 476763468, 467454933, 458337799, 449407686, 440660332, 432091596, 423697445, 415473956, 407417313, 399523800, 391789798, 384211783, 376786325, 369510080, 362379791, 355392284, 348544464, 341833317, 335255900, 328809347]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 709).prefactor = (2314333647607963/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 709).cutoff/(generalMeanRows 709).c)).2 =
    (201267572999373/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 709).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 709).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 709).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 709

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 709).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 709).criticalRate j.val*(generalMeanRows 709).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 709).c*(generalMeanRows 709).criticalPoint j.val)).2-
      (generalMeanRows 709).J/2-(generalMeanRows 709).error (generalMeanGrid j.val)+
      (generalMeanRows 709).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 709).c)).2-
      (generalMeanRows 709).J/2-(generalMeanRows 709).error 4 := by
  have he : (generalMeanRows 709).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 709) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 709)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0709

/-! Kernel-checked entropy margins for general spectral rectangle 710. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0710
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5181283813, 5012760216, 4851671165, 4697591568, 4550126478, 4408908457, 4273595224, 4143867559, 4019427409, 3899996191, 3785313258, 3675134512, 3569231150, 3467388514, 3369405058, 3275091394, 3184269428, 3096771566, 3012439981, 2931125954, 2852689251, 2776997559, 2703925966, 2633356479, 2565177574, 2499283787, 2435575333, 2373957748, 2314341563, 2256641996, 2200778669, 2146675343, 2094259672, 2043462970, 1994220002, 1946468777, 1900150367, 1855208728, 1811590537, 1769245040, 1728123907, 1688181098, 1649372737, 1611656993, 1574993969, 1539345599, 1504675548, 1470949119, 1438133171, 1406196030, 1375107420, 1344838385, 1315361225, 1286649427, 1258677609, 1231421460, 1204857689, 1178963971, 1153718901, 1129101948, 1105093413, 1081674387, 1058826715, 1036532958, 1014776358, 993540809, 972810825, 952571507, 932808523, 913508076, 894656881, 876242143, 858251534, 840673171, 823495598, 806707766, 790299014, 774259054, 758577955, 743246126, 728254300, 713593526, 699255150, 685230804, 671512396, 658092097, 644962329, 632115758, 619545283, 607244024, 595205316, 583422702, 571889920, 560600899, 549549752, 538730766, 528138399, 517767270, 507612156, 497667986, 487929831, 478392904, 469052555, 459904262, 450943628, 442166379, 433568357, 425145517, 416893923, 408809745, 400889254, 393128819, 385524905, 378074069, 370772956, 363618298, 356606909, 349735686, 343001602, 336401706, 329933120]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 710).prefactor = (232224335482449/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 710).cutoff/(generalMeanRows 710).c)).2 =
    (201267572999373/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 710).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 710).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 710).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 710

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 710).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 710).criticalRate j.val*(generalMeanRows 710).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 710).c*(generalMeanRows 710).criticalPoint j.val)).2-
      (generalMeanRows 710).J/2-(generalMeanRows 710).error (generalMeanGrid j.val)+
      (generalMeanRows 710).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 710).c)).2-
      (generalMeanRows 710).J/2-(generalMeanRows 710).error 4 := by
  have he : (generalMeanRows 710).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 710) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 710)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0710

/-! Kernel-checked entropy margins for general spectral rectangle 711. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0711
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5114901208, 4946124565, 4784806801, 4630522801, 4482877525, 4341503381, 4206057884, 4076221553, 3951696036, 3832202409, 3717479650, 3607283257, 3501383992, 3399566744, 3301629490, 3207382353, 3116646730, 3029254510, 2945047341, 2863875968, 2785599618, 2710085436, 2637207966, 2566848668, 2498895476, 2433242385, 2369789069, 2308440532, 2249106774, 2191702491, 2136146788, 2082362916, 2030278027, 1979822942, 1930931940, 1883542554, 1837595389, 1793033943, 1749804446, 1707855705, 1667138962, 1627607761, 1589217816, 1551926899, 1515694727, 1480482856, 1446254582, 1412974854, 1380610182, 1349128557, 1318499375, 1288693363, 1259682512, 1231440012, 1203940192, 1177158462, 1151071259, 1125655998, 1100891020, 1076755550, 1053229653, 1030294192, 1007930793, 986121805, 964850266, 944099873, 923854951, 904100420, 884821772, 866005041, 847636783, 829704046, 812194354, 795095681, 778396434, 762085434, 746151895, 730585410, 715375932, 700513761, 685989527, 671794180, 657918970, 644355440, 631095413, 618130977, 605454480, 593058513, 580935906, 569079715, 557483214, 546139885, 535043415, 524187680, 513566745, 503174854, 493006421, 483056027, 473318413, 463788474, 454461251, 445331929, 436395831, 427648412, 419085254, 410702063, 402494666, 394459002, 386591121, 378887184, 371343450, 363956283, 356722141, 349637577, 342699232, 335903838, 329248210, 322729244, 316343918, 310089284, 303962470]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 711).prefactor = (2323821941964439/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 711).cutoff/(generalMeanRows 711).c)).2 =
    (392187457384243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 711).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 711).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 711).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 711

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 711).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 711).criticalRate j.val*(generalMeanRows 711).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 711).c*(generalMeanRows 711).criticalPoint j.val)).2-
      (generalMeanRows 711).J/2-(generalMeanRows 711).error (generalMeanGrid j.val)+
      (generalMeanRows 711).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 711).c)).2-
      (generalMeanRows 711).J/2-(generalMeanRows 711).error 4 := by
  have he : (generalMeanRows 711).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 711) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 711)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0711

/-! Kernel-checked entropy margins for general spectral rectangle 712. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0712
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5047895349, 4878946292, 4717491364, 4563103799, 4415386994, 4273971872, 4138514539, 4008694176, 3884211152, 3764785328, 3650154523, 3540073124, 3434310834, 3332651527, 3234892209, 3140842070, 3050321616, 2963161877, 2879203679, 2798296976, 2720300236, 2645079872, 2572509726, 2502470582, 2434849722, 2369540513, 2306442029, 2245458688, 2186499933, 2129479918, 2074317227, 2020934611, 1969258736, 1919219958, 1870752105, 1823792279, 1778280663, 1734160355, 1691377193, 1649879612, 1609618492, 1570547026, 1532620594, 1495796644, 1460034580, 1425295657, 1391542882, 1358740924, 1326856023, 1295855911, 1265709736, 1236387983, 1207862412, 1180105990, 1153092833, 1126798145, 1101198164, 1076270114, 1051992154, 1028343334, 1005303549, 982853502, 960974661, 939649226, 918860094, 898590825, 878825611, 859549249, 840747108, 822405110, 804509699, 787047820, 770006896, 753374806, 737139866, 721290811, 705816772, 690707263, 675952165, 661541706, 647466451, 633717284, 620285397, 607162277, 594339694, 581809686, 569564553, 557596844, 545899346, 534465078, 523287277, 512359395, 501675085, 491228196, 481012768, 471023020, 461253346, 451698306, 442352625, 433211182, 424269004, 415521265, 406963278, 398590489, 390398473, 382382934, 374539691, 366864682, 359353959, 352003680, 344810108, 337769610, 330878647, 324133777, 317531650, 311069003, 304742661, 298549529, 292486595, 286550923, 280739653]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 712).prefactor = (4663659754216893/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 712).cutoff/(generalMeanRows 712).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 712).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 712).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 712).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 712

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 712).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 712).criticalRate j.val*(generalMeanRows 712).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 712).c*(generalMeanRows 712).criticalPoint j.val)).2-
      (generalMeanRows 712).J/2-(generalMeanRows 712).error (generalMeanGrid j.val)+
      (generalMeanRows 712).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 712).c)).2-
      (generalMeanRows 712).J/2-(generalMeanRows 712).error 4 := by
  have he : (generalMeanRows 712).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 712) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 712)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0712

/-! Kernel-checked entropy margins for general spectral rectangle 713. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0713
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5112636118, 4943909505, 4782652860, 4628439483, 4480872901, 4339584228, 4204229810, 4074489116, 3950062846, 3830671227, 3716052477, 3605961413, 3500168189, 3398457153, 3300625806, 3206483843, 3115852291, 3028562713, 2944456471, 2863384064, 2785204508, 2709784768, 2636999236, 2566729248, 2498862634, 2433293309, 2369920885, 2308650320, 2249391587, 2192059363, 2136572752, 2082855012, 2030833311, 1980438497, 1931604881, 1884270038, 1838374618, 1793862170, 1750678978, 1708773909, 1668098267, 1628605658, 1590251865, 1552994728, 1516794032, 1481611402, 1447410207, 1414155466, 1381813759, 1350353149, 1319743101, 1289954412, 1260959142, 1232730550, 1205243030, 1178472058, 1152394137, 1126986744, 1102228282, 1078098036, 1054576131, 1031643487, 1009281786, 987473430, 966201512, 945449779, 925202606, 905444961, 886162382, 867340949, 848967260, 831028406, 813511951, 796405909, 779698724, 763379252, 747436744, 731860823, 716641478, 701769037, 687234161, 673027827, 659141313, 645566189, 632294300, 619317760, 606628938, 594220448, 582085141, 570216090, 558606590, 547250142, 536140446, 525271398, 514637077, 504231740, 494049816, 484085900, 474334745, 464791256, 455450486, 446307632, 437358024, 428597128, 420020535, 411623960, 403403234, 395354306, 387473233, 379756181, 372199417, 364799307, 357552317, 350455004, 343504013, 336696081, 330028025, 323496746, 317099223, 310832514, 304693747]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 713).prefactor = (2330180095078503/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 713).cutoff/(generalMeanRows 713).c)).2 =
    (4937703919809/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 713).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 713).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 713).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 713

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 713).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 713).criticalRate j.val*(generalMeanRows 713).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 713).c*(generalMeanRows 713).criticalPoint j.val)).2-
      (generalMeanRows 713).J/2-(generalMeanRows 713).error (generalMeanGrid j.val)+
      (generalMeanRows 713).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 713).c)).2-
      (generalMeanRows 713).J/2-(generalMeanRows 713).error 4 := by
  have he : (generalMeanRows 713).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 713) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 713)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0713

/-! Kernel-checked entropy margins for general spectral rectangle 714. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0714
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5130109595, 4960806324, 4798998551, 4644258119, 4496187198, 4354415643, 4218598623, 4088414514, 3963562991, 3843763327, 3728752845, 3618285521, 3512130727, 3410072074, 3311906367, 3217442655, 3126501352, 3038913443, 2954519751, 2873170263, 2794723512, 2719046010, 2646011719, 2575501569, 2507403007, 2441609585, 2378020573, 2316540604, 2257079341, 2199551173, 2143874925, 2089973593, 2037774098, 1987207049, 1938206535, 1890709915, 1844657638, 1799993059, 1756662280, 1714613992, 1673799333, 1634171750, 1595686875, 1558302404, 1521977984, 1486675111, 1452357027, 1418988630, 1386536389, 1354968256, 1324253592, 1294363094, 1265268727, 1236943658, 1209362193, 1182499727, 1156332679, 1130838451, 1105995371, 1081782656, 1058180360, 1035169339, 1012731212, 990848322, 969503703, 948681047, 928364674, 908539503, 889191022, 870305263, 851868778, 833868615, 816292294, 799127788, 782363503, 765988257, 749991261, 734362107, 719090746, 704167476, 689582924, 675328037, 661394063, 647772543, 634455294, 621434404, 608702216, 596251318, 584074535, 572164920, 560515742, 549120481, 537972816, 527066620, 516395954, 505955055, 495738332, 485740363, 475955881, 466379775, 457007081, 447832979, 438852785, 430061947, 421456041, 413030768, 404781947, 396705510, 388797502, 381054075, 373471484, 366046083, 358774325, 351652755, 344678008, 337846808, 331155963, 324602362, 318182974, 311894847, 305735100]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 714).prefactor = (1169071980380459/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 714).cutoff/(generalMeanRows 714).c)).2 =
    (4937703919809/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 714).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 714).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 714).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 714

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 714).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 714).criticalRate j.val*(generalMeanRows 714).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 714).c*(generalMeanRows 714).criticalPoint j.val)).2-
      (generalMeanRows 714).J/2-(generalMeanRows 714).error (generalMeanGrid j.val)+
      (generalMeanRows 714).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 714).c)).2-
      (generalMeanRows 714).J/2-(generalMeanRows 714).error 4 := by
  have he : (generalMeanRows 714).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 714) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 714)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0714

/-! Kernel-checked entropy margins for general spectral rectangle 715. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0715
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5065290493, 4895759234, 4733747930, 4578828343, 4430602502, 4288700061, 4152775940, 4022508213, 3897596218, 3777758851, 3662733026, 3552272284, 3446145535, 3344135909, 3246039710, 3151665472, 3060833083, 2973372990, 2889125470, 2807939961, 2729674443, 2654194868, 2581374644, 2511094144, 2443240261, 2377705996, 2314390072, 2253196582, 2194034654, 2136818146, 2081465364, 2027898790, 1976044839, 1925833627, 1877198753, 1830077102, 1784408653, 1740136305, 1697205712, 1655565129, 1615165268, 1575959161, 1537902034, 1500951189, 1465065888, 1430207253, 1396338166, 1363423171, 1331428394, 1300321456, 1270071396, 1240648599, 1212024729, 1184172658, 1157066413, 1130681113, 1104992914, 1079978961, 1055617339, 1031887025, 1008767845, 986240434, 964286198, 942887275, 922026504, 901687386, 881854061, 862511272, 843644339, 825239134, 807282055, 789760002, 772660354, 755970950, 739680065, 723776393, 708249030, 693087454, 678281509, 663821391, 649697632, 635901086, 622422912, 609254570, 596387800, 583814613, 571527283, 559518333, 547780526, 536306855, 525090535, 514124995, 503403867, 492920978, 482670348, 472646175, 462842834, 453254867, 443876981, 434704036, 425731043, 416953159, 408365681, 399964039, 391743794, 383700633, 375830362, 368128905, 360592300, 353216691, 345998331, 338933570, 332018861, 325250748, 318625870, 312140953, 305792810, 299578336, 293494509, 287538383, 281707088]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 715).prefactor = (4679730815502219/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 715).cutoff/(generalMeanRows 715).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 715).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 715).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 715).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 715

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 715).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 715).criticalRate j.val*(generalMeanRows 715).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 715).c*(generalMeanRows 715).criticalPoint j.val)).2-
      (generalMeanRows 715).J/2-(generalMeanRows 715).error (generalMeanGrid j.val)+
      (generalMeanRows 715).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 715).c)).2-
      (generalMeanRows 715).J/2-(generalMeanRows 715).error 4 := by
  have he : (generalMeanRows 715).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 715) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 715)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0715

/-! Kernel-checked entropy margins for general spectral rectangle 716. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0716
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5082745582, 4912630115, 4750060517, 4594607074, 4445870444, 4303479004, 4167086486, 4036369854, 3911027410, 3790777081, 3675354874, 3564513483, 3458021019, 3355659865, 3257225625, 3162526172, 3071380773, 2983619290, 2899081452, 2817616177, 2739080953, 2663341275, 2590270111, 2519747423, 2451659714, 2385899616, 2322365505, 2260961141, 2201595339, 2144181663, 2088638134, 2034886968, 1982854328, 1932470087, 1883667616, 1836383583, 1790557759, 1746132848, 1703054315, 1661270239, 1620731159, 1581389947, 1543201674, 1506123495, 1470114533, 1435135775, 1401149974, 1368121553, 1336016522, 1304802389, 1274448086, 1244923898, 1216201389, 1188253340, 1161053686, 1134577462, 1108800741, 1083700590, 1059255017, 1035442928, 1012244078, 989639037, 967609147, 946136483, 925203825, 904794619, 884892948, 865483502, 846551554, 828082924, 810063965, 792481530, 775322957, 758576040, 742229016, 726270540, 710689670, 695475846, 680618880, 666108933, 651936503, 638092413, 624567794, 611354073, 598442964, 585826450, 573496777, 561446444, 549668188, 538154979, 526900008, 515896680, 505138606, 494619593, 484333639, 474274922, 464437799, 454816792, 445406590, 436202034, 427198120, 418389988, 409772917, 401342323, 393093751, 385022872, 377125480, 369397484, 361834908, 354433883, 347190648, 340101542, 333163004, 326371568, 319723861, 313216597, 306846578, 300610689, 294505897, 288529246, 282677856]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 716).prefactor = (1173964314493521/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 716).cutoff/(generalMeanRows 716).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 716).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 716).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 716).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 716

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 716).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 716).criticalRate j.val*(generalMeanRows 716).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 716).c*(generalMeanRows 716).criticalPoint j.val)).2-
      (generalMeanRows 716).J/2-(generalMeanRows 716).error (generalMeanGrid j.val)+
      (generalMeanRows 716).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 716).c)).2-
      (generalMeanRows 716).J/2-(generalMeanRows 716).error 4 := by
  have he : (generalMeanRows 716).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 716) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 716)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0716

/-! Kernel-checked entropy margins for general spectral rectangle 717. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0717
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5067774023, 4898196191, 4736126905, 4581139525, 4432837524, 4290851859, 4154838628, 4024476971, 3899467180, 3779529011, 3664400151, 3553834832, 3447602582, 3345487079, 3247285121, 3152805672, 3061869002, 2974305896, 2889956923, 2808671777, 2730308655, 2654733702, 2581820481, 2511449501, 2443507763, 2377888357, 2314490076, 2253217061, 2193978478, 2136688208, 2081264563, 2027630026, 1975710998, 1925437574, 1876743326, 1829565103, 1783842841, 1739519394, 1696540365, 1654853953, 1614410811, 1575163911, 1537068415, 1500081559, 1464162542, 1429272416, 1395373994, 1362431753, 1330411750, 1299281537, 1269010085, 1239567712, 1210926012, 1183057793, 1155937017, 1129538735, 1103839044, 1078815026, 1054444703, 1030706994, 1007581666, 985049299, 963091243, 941689583, 920827103, 900487258, 880654135, 861312430, 842447419, 824044927, 806091310, 788573426, 771478614, 754794673, 738509842, 722612779, 707092545, 691938584, 677140710, 662689086, 648574215, 634786923, 621318343, 608159907, 595303330, 582740602, 570463972, 558465941, 546739252, 535276879, 524072017, 513118077, 502408674, 491937620, 481698917, 471686750, 461895480, 452319636, 442953911, 433793153, 424832364, 416066690, 407491415, 399101963, 390893884, 382862856, 375004680, 367315271, 359790658, 352426983, 345220488, 338167520, 331264526, 324508047, 317894714, 311421251, 305084466, 298881252, 292808581, 286863506, 281043153]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 717).prefactor = (4666973719460147/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 717).cutoff/(generalMeanRows 717).c)).2 =
    (381903859841009/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 717).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 717).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 717).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 717

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 717).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 717).criticalRate j.val*(generalMeanRows 717).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 717).c*(generalMeanRows 717).criticalPoint j.val)).2-
      (generalMeanRows 717).J/2-(generalMeanRows 717).error (generalMeanGrid j.val)+
      (generalMeanRows 717).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 717).c)).2-
      (generalMeanRows 717).J/2-(generalMeanRows 717).error 4 := by
  have he : (generalMeanRows 717).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 717) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 717)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0717

/-! Kernel-checked entropy margins for general spectral rectangle 718. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0718
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5002146497, 4832424804, 4670246836, 4515184253, 4366838919, 4224840271, 4088842959, 3958524747, 3833584621, 3713741090, 3598730652, 3488306407, 3382236797, 3280304467, 3182305220, 3088047073, 2997349387, 2910042073, 2825964866, 2744966654, 2666904868, 2591644908, 2519059629, 2449028854, 2381438929, 2316182309, 2253157180, 2192267098, 2133420666, 2076531222, 2021516556, 1968298649, 1916803419, 1866960495, 1818702999, 1771967349, 1726693066, 1682822603, 1640301175, 1599076613, 1559099211, 1520321596, 1482698601, 1446187142, 1410746110, 1376336263, 1342920129, 1310461914, 1278927410, 1248283916, 1218500162, 1189546231, 1161393494, 1134014544, 1107383134, 1081474120, 1056263405, 1031727890, 1007845422, 984594752, 961955487, 939908051, 918433648, 897514221, 877132421, 857271573, 837915641, 819049204, 800657424, 782726022, 765241252, 748189874, 731559136, 715336749, 699510869, 684070077, 669003357, 654300086, 639950007, 625943225, 612270181, 598921645, 585888700, 573162728, 560735399, 548598659, 536744718, 525166041, 513855337, 502805547, 492009839, 481461596, 471154410, 461082072, 451238564, 441618054, 432214887, 423023580, 414038815, 405255430, 396668419, 388272922, 380064221, 372037734, 364189012, 356513733, 349007699, 341666829, 334487157, 327464829, 320596095, 313877310, 307304929, 300875503, 294585675, 288432182, 282411844, 276521567, 270758339, 265119228, 259601376]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 718).prefactor = (4683190257502811/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 718).cutoff/(generalMeanRows 718).c)).2 =
    (93624104640787/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 718).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 718).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 718).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 718

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 718).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 718).criticalRate j.val*(generalMeanRows 718).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 718).c*(generalMeanRows 718).criticalPoint j.val)).2-
      (generalMeanRows 718).J/2-(generalMeanRows 718).error (generalMeanGrid j.val)+
      (generalMeanRows 718).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 718).c)).2-
      (generalMeanRows 718).J/2-(generalMeanRows 718).error 4 := by
  have he : (generalMeanRows 718).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 718) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 718)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0718

/-! Kernel-checked entropy margins for general spectral rectangle 719. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0719
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5022229167, 4851874422, 4689077895, 4533411364, 4384476766, 4241903562, 4105346394, 3974482976, 3849012219, 3728652522, 3613140251, 3502228348, 3395685081, 3293292898, 3194847392, 3100156357, 3009038916, 2921324736, 2836853296, 2755473224, 2677041682, 2601423801, 2528492160, 2458126305, 2390212304, 2324642334, 2261314302, 2200131488, 2141002218, 2083839557, 2028561025, 1975088334, 1923347139, 1873266807, 1824780206, 1777823500, 1732335962, 1688259804, 1645540004, 1604124157, 1563962333, 1525006934, 1487212577, 1450535965, 1414935783, 1380372588, 1346808713, 1314208171, 1282536570, 1251761029, 1221850101, 1192773701, 1164503034, 1137010532, 1110269795, 1084255526, 1058943484, 1034310428, 1010334068, 986993023, 964266772, 942135615, 920580636, 899583663, 879127235, 859194568, 839769522, 820836575, 802380793, 784387802, 766843764, 749735354, 733049735, 716774536, 700897835, 685408137, 670294354, 655545791, 641152126, 627103396, 613389982, 600002593, 586932252, 574170286, 561708311, 549538222, 537652178, 526042596, 514702139, 503623703, 492800415, 482225615, 471892856, 461795890, 451928664, 442285311, 432860140, 423647638, 414642453, 405839396, 397233430, 388819667, 380593363, 372549911, 364684837, 356993796, 349472566, 342117044, 334923244, 327887291, 321005416, 314273956, 307689348, 301248125, 294946915, 288782437, 282751497, 276850987, 271077880, 265429231, 259902169]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 719).prefactor = (4686667581016313/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 719).cutoff/(generalMeanRows 719).c)).2 =
    (46460434648317/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 719).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 719).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 719).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 719

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 719).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 719).criticalRate j.val*(generalMeanRows 719).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 719).c*(generalMeanRows 719).criticalPoint j.val)).2-
      (generalMeanRows 719).J/2-(generalMeanRows 719).error (generalMeanGrid j.val)+
      (generalMeanRows 719).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 719).c)).2-
      (generalMeanRows 719).J/2-(generalMeanRows 719).error 4 := by
  have he : (generalMeanRows 719).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 719) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 719)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0719

/-! Kernel-checked entropy margins for general spectral rectangle 720. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0720
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4957951108, 4787479739, 4624601673, 4468886945, 4319935840, 4177376258, 4040861355, 3910067440, 3784692081, 3664452406, 3549083564, 3438337339, 3331980893, 3229795617, 3131576095, 3037129154, 2946272992, 2858836390, 2774657979, 2693585573, 2615475552, 2540192300, 2467607676, 2397600535, 2330056284, 2264866463, 2201928365, 2141144685, 2082423181, 2025676376, 1970821269, 1917779067, 1866474944, 1816837802, 1768800063, 1722297460, 1677268856, 1633656063, 1591403678, 1550458931, 1510771536, 1472293558, 1434979288, 1398785115, 1363669424, 1329592482, 1296516345, 1264404759, 1233223075, 1202938169, 1173518358, 1144933329, 1117154072, 1090152811, 1063902946, 1038378990, 1013556521, 989412121, 965923335, 943068620, 920827304, 899179542, 878106277, 857589206, 837610739, 818153973, 799202654, 780741150, 762754423, 745228001, 728147952, 711500863, 695273812, 679454350, 664030480, 648990635, 634323662, 620018803, 606065677, 592454266, 579174899, 566218237, 553575259, 541237251, 529195791, 517442735, 505970213, 494770612, 483836565, 473160948, 462736861, 452557628, 442616784, 432908065, 423425405, 414162926, 405114930, 396275893, 387640462, 379203441, 370959794, 362904631, 355033210, 347340927, 339823311, 332476024, 325294850, 318275696, 311414583, 304707647, 298151132, 291741387, 285474862, 279348105, 273357760, 267500561, 261773333, 256172984, 250696509, 245340978, 240103544]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 720).prefactor = (94061782788551/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 720).cutoff/(generalMeanRows 720).c)).2 =
    (14573220115251/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 720).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 720).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 720).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 720

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 720).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 720).criticalRate j.val*(generalMeanRows 720).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 720).c*(generalMeanRows 720).criticalPoint j.val)).2-
      (generalMeanRows 720).J/2-(generalMeanRows 720).error (generalMeanGrid j.val)+
      (generalMeanRows 720).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 720).c)).2-
      (generalMeanRows 720).J/2-(generalMeanRows 720).error 4 := by
  have he : (generalMeanRows 720).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 720) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 720)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0720

/-! Kernel-checked entropy margins for general spectral rectangle 721. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0721
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5019527675, 4849216242, 4686474747, 4530873361, 4382012566, 4239520509, 4103050641, 3972279606, 3846905345, 3726645388, 3611235319, 3500427378, 3393989203, 3291702684, 3193362915, 3098777246, 3007764408, 2920153724, 2835784370, 2754504710, 2676171679, 2600650210, 2527812716, 2457538602, 2389713819, 2324230449, 2260986324, 2199884665, 2140833756, 2083746636, 2028540808, 1975137983, 1923463820, 1873447704, 1825022526, 1778124482, 1732692882, 1688669980, 1646000802, 1604632994, 1564516681, 1525604325, 1487850599, 1451212272, 1415648091, 1381118679, 1347586433, 1315015433, 1283371355, 1252621383, 1222734138, 1193679599, 1165429039, 1137954954, 1111231007, 1085231966, 1059933650, 1035312880, 1011347427, 988015967, 965298035, 943173990, 921624969, 900632853, 880180232, 860250372, 840827183, 821895190, 803439503, 785445795, 767900269, 750789642, 734101116, 717822361, 701941490, 686447045, 671327973, 656573611, 642173670, 628118217, 614397663, 601002744, 587924513, 575154322, 562683811, 550504899, 538609769, 526990859, 515640852, 504552667, 493719447, 483134552, 472791551, 462684214, 452806502, 443152563, 433716723, 424493479, 415477494, 406663589, 398046741, 389622071, 381384846, 373330469, 365454475, 357752527, 350220411, 342854034, 335649415, 328602685, 321710084, 314967953, 308372735, 301920968, 295609285, 289434410, 283393152, 277482408, 271699155, 266040449, 260503425]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 721).prefactor = (2349731571930329/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 721).cutoff/(generalMeanRows 721).c)).2 =
    (93624104640787/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 721).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 721).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 721).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 721

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 721).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 721).criticalRate j.val*(generalMeanRows 721).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 721).c*(generalMeanRows 721).criticalPoint j.val)).2-
      (generalMeanRows 721).J/2-(generalMeanRows 721).error (generalMeanGrid j.val)+
      (generalMeanRows 721).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 721).c)).2-
      (generalMeanRows 721).J/2-(generalMeanRows 721).error 4 := by
  have he : (generalMeanRows 721).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 721) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 721)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0721

/-! Kernel-checked entropy margins for general spectral rectangle 722. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0722
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4954942262, 4784518740, 4621700095, 4466054766, 4317181592, 4174707167, 4038283467, 3907585733, 3782310575, 3662174253, 3546911142, 3436272330, 3330024353, 3227948048, 3129837503, 3035499107, 2944750669, 2857420629, 2773347317, 2692378287, 2614369694, 2539185727, 2466698080, 2396785470, 2329333188, 2264232680, 2201381168, 2140681287, 2082040757, 2025372074, 1970592221, 1917622406, 1866387808, 1816817348, 1768843470, 1722401942, 1677431663, 1633874489, 1591675065, 1550780672, 1511141081, 1472708415, 1435437024, 1399283361, 1364205875, 1330164898, 1297122552, 1265042649, 1233890609, 1203633373, 1174239324, 1145678217, 1117921107, 1090940284, 1064709211, 1039202466, 1014395686, 990265517, 966789563, 943946340, 921715232, 900076451, 879010995, 858500612, 838527767, 819075605, 800127921, 781669130, 763684241, 746158825, 729078995, 712431377, 696203091, 680381726, 664955322, 649912348, 635241687, 620932612, 606974777, 593358192, 580073218, 567110543, 554461174, 542116422, 530067890, 518307461, 506827285, 495619771, 484677575, 473993591, 463560940, 453372963, 443423212, 433705441, 424213599, 414941823, 405884429, 397035908, 388390918, 379944278, 371690960, 363626087, 355744927, 348042886, 340515504, 333158448, 325967513, 318938612, 312067776, 305351146, 298784972, 292365610, 286089515, 279953241, 273953437, 268086841, 262350283, 256740675, 251255013, 245890375, 240643914]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 722).prefactor = (2357896287164823/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 722).cutoff/(generalMeanRows 722).c)).2 =
    (367143444257889/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 722).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 722).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 722).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 722

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 722).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 722).criticalRate j.val*(generalMeanRows 722).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 722).c*(generalMeanRows 722).criticalPoint j.val)).2-
      (generalMeanRows 722).J/2-(generalMeanRows 722).error (generalMeanGrid j.val)+
      (generalMeanRows 722).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 722).c)).2-
      (generalMeanRows 722).J/2-(generalMeanRows 722).error 4 := by
  have he : (generalMeanRows 722).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 722) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 722)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0722

/-! Kernel-checked entropy margins for general spectral rectangle 723. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0723
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4894910418, 4724353406, 4561424401, 4405691663, 4256753802, 4114237127, 3977793293, 3847097176, 3721844989, 3601752565, 3486553825, 3375999379, 3269855270, 3167901822, 3069932599, 2975753452, 2885181648, 2798045075, 2714181508, 2633437944, 2555669980, 2480741246, 2408522881, 2338893050, 2271736495, 2206944120, 2144412608, 2084044066, 2025745691, 1969429465, 1915011867, 1862413607, 1811559379, 1762377626, 1714800327, 1668762794, 1624203481, 1581063809, 1539288001, 1498822925, 1459617951, 1421624812, 1384797478, 1349092036, 1314466575, 1280881084, 1248297346, 1216678852, 1185990704, 1156199541, 1127273453, 1099181911, 1071895695, 1045386833, 1019628532, 994595126, 970262017, 946605624, 923603332, 901233449, 879475157, 858308476, 837714219, 817673958, 798169987, 779185291, 760703509, 742708909, 725186359, 708121296, 691499705, 675308090, 659533456, 644163282, 629185506, 614588497, 600361043, 586492333, 572971936, 559789785, 546936165, 534401699, 522177328, 510254302, 498624169, 487278759, 476210175, 465410781, 454873191, 444590261, 434555078, 424760953, 415201409, 405870174, 396761176, 387868531, 379186538, 370709674, 362432583, 354350075, 346457116, 338748822, 331220457, 323867425, 316685267, 309669653, 302816379, 296121367, 289580651, 283190382, 276946821, 270846333, 264885388, 259060551, 253368486, 247805950, 242369786, 237056926, 231864385, 226789260, 221828725]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 723).prefactor = (2359784118570319/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 723).cutoff/(generalMeanRows 723).c)).2 =
    (357031200399663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 723).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 723).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 723).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 723

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 723).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 723).criticalRate j.val*(generalMeanRows 723).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 723).c*(generalMeanRows 723).criticalPoint j.val)).2-
      (generalMeanRows 723).J/2-(generalMeanRows 723).error (generalMeanGrid j.val)+
      (generalMeanRows 723).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 723).c)).2-
      (generalMeanRows 723).J/2-(generalMeanRows 723).error 4 := by
  have he : (generalMeanRows 723).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 723) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 723)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0723

/-! Kernel-checked entropy margins for general spectral rectangle 724. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0724
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4912061636, 4740907011, 4577407121, 4421128713, 4271668990, 4128652954, 3991731035, 3860576974, 3734885917, 3614372703, 3498770319, 3387828503, 3281312476, 3179001795, 3080689299, 2986180159, 2895291002, 2807849111, 2723691696, 2642665216, 2564624761, 2489433485, 2416962075, 2347088269, 2279696405, 2214677005, 2151926390, 2091346323, 2032843678, 1976330126, 1921721854, 1868939296, 1817906880, 1768552799, 1720808795, 1674609952, 1629894508, 1586603679, 1544681494, 1504074633, 1464732289, 1426606026, 1389649654, 1353819104, 1319072319, 1285369148, 1252671240, 1220941958, 1190146283, 1160250735, 1131223293, 1103033321, 1075651498, 1049049751, 1023201196, 998080076, 973661707, 949922424, 926839535, 904391270, 882556740, 861315893, 840649476, 820538996, 800966686, 781915469, 763368928, 745311278, 727727331, 710602474, 693922642, 677674294, 661844387, 646420358, 631390101, 616741946, 602464641, 588547337, 574979565, 561751225, 548852568, 536274183, 524006978, 512042176, 500371292, 488986130, 477878762, 467041528, 456467015, 446148055, 436077711, 426249268, 416656228, 407292298, 398151383, 389227578, 380515165, 372008599, 363702506, 355591678, 347671063, 339935760, 332381016, 325002221, 317794897, 310754700, 303877414, 297158943, 290595309, 284182650, 277917212, 271795349, 265813516, 259968270, 254256261, 248674234, 243219022, 237887547, 232676812, 227583904, 222605988]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 724).prefactor = (947221015153373/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 724).cutoff/(generalMeanRows 724).c)).2 =
    (357031200399663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 724).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 724).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 724).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 724

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 724).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 724).criticalRate j.val*(generalMeanRows 724).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 724).c*(generalMeanRows 724).criticalPoint j.val)).2-
      (generalMeanRows 724).J/2-(generalMeanRows 724).error (generalMeanGrid j.val)+
      (generalMeanRows 724).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 724).c)).2-
      (generalMeanRows 724).J/2-(generalMeanRows 724).error 4 := by
  have he : (generalMeanRows 724).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 724) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 724)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0724

/-! Kernel-checked entropy margins for general spectral rectangle 725. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0725
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5033868168, 4863025999, 4699790983, 4543730224, 4394441396, 4251550069, 4114707330, 3983587658, 3857887001, 3737321067, 3621623763, 3510545792, 3403853381, 3301327124, 3202760926, 3107961047, 3016745217, 2928941839, 2844389249, 2762935039, 2684435434, 2608754719, 2535764713, 2465344277, 2397378862, 2331760097, 2268385394, 2207157595, 2147984635, 2090779234, 2035458608, 1981944199, 1930161429, 1880039462, 1831510989, 1784512024, 1738981713, 1694862159, 1652098253, 1610637519, 1570429970, 1531427966, 1493586091, 1456861031, 1421211461, 1386597935, 1352982793, 1320330060, 1288605363, 1257775846, 1227810089, 1198678040, 1170350938, 1142801254, 1116002627, 1089929802, 1064558583, 1039865771, 1015829123, 992427302, 969639833, 947447064, 925830122, 904770881, 884251925, 864256514, 844768551, 825772556, 807253638, 789197461, 771590228, 754418651, 737669930, 721331731, 705392165, 689839770, 674663490, 659852660, 645396989, 631286540, 617511720, 604063264, 590932220, 578109937, 565588053, 553358483, 541413404, 529745253, 518346708, 507210683, 496330317, 485698966, 475310195, 465157767, 455235640, 445537956, 436059036, 426793372, 417735620, 408880598, 400223274, 391758767, 383482335, 375389376, 367475419, 359736119, 352167259, 344764736, 337524565, 330442871, 323515885, 316739942, 310111479, 303627028, 297283214, 291076753, 285004451, 279063194, 273249954, 267561781, 261995801]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 725).prefactor = (4728277050513661/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 725).cutoff/(generalMeanRows 725).c)).2 =
    (377317294904789/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 725).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 725).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 725).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 725

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 725).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 725).criticalRate j.val*(generalMeanRows 725).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 725).c*(generalMeanRows 725).criticalPoint j.val)).2-
      (generalMeanRows 725).J/2-(generalMeanRows 725).error (generalMeanGrid j.val)+
      (generalMeanRows 725).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 725).c)).2-
      (generalMeanRows 725).J/2-(generalMeanRows 725).error 4 := by
  have he : (generalMeanRows 725).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 725) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 725)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0725

/-! Kernel-checked entropy margins for general spectral rectangle 726. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0726
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5153169518, 4980697018, 4815874938, 4658267611, 4507470162, 4363105820, 4224823515, 4092295740, 3965216615, 3843300159, 3726278721, 3613901568, 3505933599, 3402154181, 3302356086, 3206344525, 3113936262, 3024958801, 2939249650, 2856655632, 2777032265, 2700243176, 2626159575, 2554659761, 2485628663, 2418957427, 2354543020, 2292287868, 2232099524, 2173890353, 2117577241, 2063081327, 2010327748, 1959245409, 1909766756, 1861827579, 1815366816, 1770326376, 1726650969, 1684287954, 1643187185, 1603300881, 1564583491, 1526991576, 1490483692, 1455020286, 1420563595, 1387077550, 1354527687, 1322881067, 1292106190, 1262172930, 1233052457, 1204717174, 1177140656, 1150297589, 1124163719, 1098715793, 1073931516, 1049789498, 1026269217, 1003350972, 981015846, 959245669, 938022978, 917330992, 897153574, 877475201, 858280941, 839556420, 821287799, 803461751, 786065437, 769086484, 752512964, 736333375, 720536624, 705112006, 690049189, 675338199, 660969403, 646933497, 633221487, 619824684, 606734685, 593943363, 581442857, 569225560, 557284111, 545611380, 534200466, 523044682, 512137550, 501472791, 491044319, 480846234, 470872813, 461118502, 451577917, 442245828, 433117160, 424186987, 415450522, 406903118, 398540258, 390357553, 382350739, 374515668, 366848308, 359344738, 352001145, 344813816, 337779141, 330893607, 324153792, 317556367, 311098088, 304775798, 298586421, 292526960, 286594496]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 726).prefactor = (1190230166624537/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 726).cutoff/(generalMeanRows 726).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 726).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 726).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 726).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 726

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 726).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 726).criticalRate j.val*(generalMeanRows 726).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 726).c*(generalMeanRows 726).criticalPoint j.val)).2-
      (generalMeanRows 726).J/2-(generalMeanRows 726).error (generalMeanGrid j.val)+
      (generalMeanRows 726).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 726).c)).2-
      (generalMeanRows 726).J/2-(generalMeanRows 726).error 4 := by
  have he : (generalMeanRows 726).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 726) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 726)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0726

/-! Kernel-checked entropy margins for general spectral rectangle 727. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0727
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5263793526, 5096295096, 4936138828, 4782904293, 4636200937, 4495665469, 4360959530, 4231767610, 4107795171, 3988766966, 3874425518, 3764529738, 3658853686, 3557185432, 3459326027, 3365088559, 3274297295, 3186786894, 3102401683, 3020994995, 2942428560, 2866571944, 2793302029, 2722502537, 2654063587, 2587881288, 2523857356, 2461898770, 2401917437, 2343829897, 2287557036, 2233023825, 2180159078, 2128895221, 2079168081, 2030916690, 1984083096, 1938612189, 1894451544, 1851551266, 1809863847, 1769344037, 1729948714, 1691636771, 1654369003, 1618108007, 1582818083, 1548465144, 1515016628, 1482441422, 1450709781, 1419793260, 1389664646, 1360297894, 1331668069, 1303751287, 1276524664, 1249966266, 1224055060, 1198770872, 1174094341, 1150006885, 1126490657, 1103528512, 1081103977, 1059201212, 1037804987, 1016900648, 996474093, 976511747, 957000534, 937927859, 919281582, 901050002, 883221833, 865786186, 848732555, 832050797, 815731118, 799764055, 784140466, 768851513, 753888652, 739243617, 724908411, 710875295, 697136778, 683685603, 670514741, 657617384, 644986928, 632616976, 620501321, 608633943, 597008999, 585620820, 574463902, 563532899, 552822619, 542328019, 532044195, 521966384, 512089951, 502410392, 492923324, 483624483, 474509720, 465574995, 456816376, 448230035, 439812243, 431559365, 423467864, 415534288, 407755276, 400127550, 392647915, 385313252, 378120521, 371066758, 364149068]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 727).prefactor = (2311632775052493/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 727).cutoff/(generalMeanRows 727).c)).2 =
    (41383648669473/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 727).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 727).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 727).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 727

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 727).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 727).criticalRate j.val*(generalMeanRows 727).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 727).c*(generalMeanRows 727).criticalPoint j.val)).2-
      (generalMeanRows 727).J/2-(generalMeanRows 727).error (generalMeanGrid j.val)+
      (generalMeanRows 727).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 727).c)).2-
      (generalMeanRows 727).J/2-(generalMeanRows 727).error 4 := by
  have he : (generalMeanRows 727).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 727) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 727)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0727

/-! Kernel-checked entropy margins for general spectral rectangle 728. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0728
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4981269577, 4807703488, 4641899985, 4483419710, 4331854191, 4186823146, 4047972081, 3914970140, 3787508173, 3665297001, 3548065850, 3435560932, 3327544160, 3223791984, 3124094325, 3028253609, 2936083879, 2847409986, 2762066845, 2679898751, 2600758754, 2524508079, 2451015591, 2380157306, 2311815931, 2245880448, 2182245715, 2120812112, 2061485200, 2004175407, 1948797738, 1895271506, 1843520075, 1793470626, 1745053938, 1698204180, 1652858723, 1608957954, 1566445110, 1525266124, 1485369470, 1446706032, 1409228966, 1372893586, 1337657240, 1303479212, 1270320611, 1238144283, 1206914715, 1176597957, 1147161537, 1118574385, 1090806769, 1063830220, 1037617475, 1012142413, 987380004, 963306249, 939898136, 917133589, 894991424, 873451306, 852493712, 832099888, 812251816, 792932179, 774124329, 755812258, 737980563, 720614427, 703699587, 687222310, 671169369, 655528025, 640286001, 625431462, 610952999, 596839609, 583080675, 569665956, 556585565, 543829957, 531389916, 519256537, 507421218, 495875645, 484611781, 473621857, 462898356, 452434008, 442221779, 432254859, 422526660, 413030797, 403761092, 394711557, 385876391, 377249972, 368826852, 360601747, 352569535, 344725247, 337064061, 329581303, 322272432, 315133044, 308158861, 301345730, 294689619, 288186609, 281832895, 275624779, 269558666, 263631064, 257838576, 252177902, 246645829, 241239237, 235955086, 230790422, 225742370]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 728).prefactor = (960566779281063/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 728).cutoff/(generalMeanRows 728).c)).2 =
    (357031200399663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 728).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 728).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 728).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 728

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 728).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 728).criticalRate j.val*(generalMeanRows 728).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 728).c*(generalMeanRows 728).criticalPoint j.val)).2-
      (generalMeanRows 728).J/2-(generalMeanRows 728).error (generalMeanGrid j.val)+
      (generalMeanRows 728).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 728).c)).2-
      (generalMeanRows 728).J/2-(generalMeanRows 728).error 4 := by
  have he : (generalMeanRows 728).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 728) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 728)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0728

/-! Kernel-checked entropy margins for general spectral rectangle 729. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0729
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4897978896, 4727382091, 4564401241, 4408606216, 4259597088, 4117001490, 3980472272, 3849685394, 3724338043, 3604146935, 3488846780, 3378188901, 3271939978, 3169880906, 3071805757, 2977520835, 2886843809, 2799602919, 2715636255, 2634791085, 2556923244, 2481896566, 2409582368, 2339858963, 2272611218, 2207730140, 2145112496, 2084660458, 2026281272, 1969886954, 1915394006, 1862723147, 1811799071, 1762550211, 1714908529, 1668809309, 1624190975, 1580994911, 1539165295, 1498648951, 1459395196, 1421355711, 1384484410, 1348737321, 1314072474, 1280449794, 1247831005, 1216179533, 1185460417, 1155640232, 1126687004, 1098570140, 1071260359, 1044729624, 1018951081, 993899004, 969548733, 945876628, 922860018, 900477151, 878707157, 857529998, 836926436, 816877990, 797366905, 778376115, 759889213, 741890420, 724364559, 707297024, 690673756, 674481221, 658706382, 643336683, 628360021, 613764732, 599539572, 585673693, 572156633, 558978297, 546128939, 533599154, 521379855, 509462269, 497837916, 486498603, 475436411, 464643681, 454113007, 443837225, 433809404, 424022834, 414471022, 405147679, 396046718, 387162239, 378488529, 370020048, 361751430, 353677471, 345793125, 338093498, 330573843, 323229555, 316056164, 309049332, 302204848, 295518623, 288986686, 282605181, 276370361, 270278585, 264326318, 258510119, 252826648, 247272656, 241844982, 236540553, 231356383, 226289562, 221337262]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 729).prefactor = (4706736702440241/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 729).cutoff/(generalMeanRows 729).c)).2 =
    (70845229894411/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 729).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 729).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 729).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 729

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 729).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 729).criticalRate j.val*(generalMeanRows 729).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 729).c*(generalMeanRows 729).criticalPoint j.val)).2-
      (generalMeanRows 729).J/2-(generalMeanRows 729).error (generalMeanGrid j.val)+
      (generalMeanRows 729).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 729).c)).2-
      (generalMeanRows 729).J/2-(generalMeanRows 729).error 4 := by
  have he : (generalMeanRows 729).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 729) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 729)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0729

/-! Kernel-checked entropy margins for general spectral rectangle 730. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0730
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4915285722, 4744086120, 4580529382, 4424183862, 4274648215, 4131548761, 3994537122, 3863288114, 3737497853, 3616882054, 3501174490, 3390125605, 3283501256, 3181081562, 3082659868, 2988041794, 2897044364, 2809495212, 2725231854, 2644101021, 2565958037, 2490666255, 2418096538, 2348126768, 2280641405, 2215531072, 2152692171, 2092026528, 2033441061, 1976847476, 1922161979, 1869305010, 1818200996, 1768778117, 1720968094, 1674705985, 1629929994, 1586581297, 1544603878, 1503944371, 1464551915, 1426378019, 1389376434, 1353503034, 1318715700, 1284974216, 1252240170, 1220476858, 1189649198, 1159723644, 1130668110, 1102451897, 1075045617, 1048421137, 1022551507, 997410909, 972974597, 949218848, 926120909, 903658954, 881812036, 860560048, 839883684, 819764398, 800184371, 781126478, 762574253, 744511862, 726924074, 709796231, 693114226, 676864475, 661033897, 645609889, 630580307, 615933447, 601658022, 587743149, 574178327, 560953426, 548058666, 535484606, 523222131, 511262435, 499597008, 488217628, 477116348, 466285482, 455717599, 445405508, 435342253, 425521103, 415935540, 406579254, 397446134, 388530263, 379825904, 371327500, 363029665, 354927177, 347014972, 339288139, 331741914, 324371675, 317172937, 310141346, 303272678, 296562827, 290007810, 283603756, 277346905, 271233605, 265260305, 259423555, 253720002, 248146384, 242699532, 237376361, 232173872, 227089148, 222119349]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 730).prefactor = (236168389045319/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 730).cutoff/(generalMeanRows 730).c)).2 =
    (70845229894411/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 730).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 730).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 730).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 730

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 730).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 730).criticalRate j.val*(generalMeanRows 730).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 730).c*(generalMeanRows 730).criticalPoint j.val)).2-
      (generalMeanRows 730).J/2-(generalMeanRows 730).error (generalMeanGrid j.val)+
      (generalMeanRows 730).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 730).c)).2-
      (generalMeanRows 730).J/2-(generalMeanRows 730).error 4 := by
  have he : (generalMeanRows 730).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 730) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 730)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0730

/-! Kernel-checked entropy margins for general spectral rectangle 731. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0731
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5249454706, 5082420525, 4922682820, 4769825634, 4623462494, 4483233822, 4348804648, 4219862545, 4096115786, 3977291680, 3863135076, 3753407001, 3647883437, 3546354200, 3448621923, 3354501130, 3263817388, 3176406530, 3092113944, 3010793921, 2932309054, 2856529683, 2783333384, 2712604503, 2644233715, 2578117623, 2514158385, 2452263366, 2392344819, 2334319584, 2278108809, 2223637696, 2170835255, 2119634080, 2069970143, 2021782593, 1975013576, 1929608063, 1885513693, 1842680615, 1801061356, 1760610687, 1721285497, 1683044678, 1645849019, 1609661101, 1574445202, 1540167208, 1506794525, 1474296001, 1442641854, 1411803594, 1381753962, 1352466867, 1323917323, 1296081397, 1268936153, 1242459606, 1216630671, 1191429122, 1166835547, 1142831312, 1119398519, 1096519976, 1074179157, 1052360178, 1031047759, 1010227203, 989884363, 970005620, 950577858, 931588441, 913025192, 894876370, 877130653, 859777120, 842805232, 826204813, 809966040, 794079421, 778535788, 763326277, 748442319, 733875625, 719618178, 705662218, 692000234, 678624952, 665529328, 652706535, 640149959, 627853187, 615810000, 604014368, 592460438, 581142532, 570055136, 559192899, 548550623, 538123257, 527905894, 517893765, 508082235, 498466795, 489043060, 479806765, 470753760, 461880007, 453181572, 444654629, 436295450, 428100402, 420065950, 412188646, 404465131, 396892131, 389466453, 382184986, 375044692, 368042612, 361175856]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 731).prefactor = (458309578226791/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 731).cutoff/(generalMeanRows 731).c)).2 =
    (408234231146061/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 731).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 731).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 731).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 731

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 731).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 731).criticalRate j.val*(generalMeanRows 731).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 731).c*(generalMeanRows 731).criticalPoint j.val)).2-
      (generalMeanRows 731).J/2-(generalMeanRows 731).error (generalMeanGrid j.val)+
      (generalMeanRows 731).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 731).c)).2-
      (generalMeanRows 731).J/2-(generalMeanRows 731).error 4 := by
  have he : (generalMeanRows 731).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 731) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 731)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0731

/-! Kernel-checked entropy margins for general spectral rectangle 732. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0732
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5267491568, 5099883466, 4939596909, 4786214515, 4639348478, 4498637987, 4363746922, 4234361780, 4110189833, 3990957454, 3876408613, 3766303518, 3660417381, 3558539294, 3460471214, 3366027027, 3275031700, 3187320502, 3102738291, 3021138858, 2942384320, 2866344575, 2792896778, 2721924876, 2653319169, 2586975905, 2522796906, 2460689219, 2400564795, 2342340188, 2285936276, 2231278003, 2178294135, 2126917036, 2077082456, 2028729336, 1981799623, 1936238099, 1891992223, 1849011972, 1807249712, 1766660057, 1727199747, 1688827535, 1651504073, 1615191815, 1579854917, 1545459145, 1511971795, 1479361608, 1447598698, 1416654479, 1386501599, 1357113875, 1328466236, 1300534667, 1273296154, 1246728635, 1220810953, 1195522812, 1170844735, 1146758023, 1123244716, 1100287563, 1077869983, 1055976034, 1034590388, 1013698293, 993285556, 973338511, 953843996, 934789332, 916162300, 897951120, 880144430, 862731271, 845701068, 829043611, 812749042, 796807838, 781210798, 765949028, 751013929, 736397185, 722090750, 708086838, 694377912, 680956673, 667816053, 654949202, 642349482, 630010459, 617925892, 606089731, 594496102, 583139308, 572013817, 561114258, 550435415, 539972221, 529719752, 519673222, 509827980, 500179501, 490723387, 481455357, 472371247, 463467003, 454738681, 446182440, 437794539, 429571334, 421509275, 413604905, 405854853, 398255832, 390804640, 383498154, 376333327, 369307188, 362416838]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 732).prefactor = (4598843068214853/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 732).cutoff/(generalMeanRows 732).c)).2 =
    (408234231146061/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 732).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 732).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 732).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 732

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 732).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 732).criticalRate j.val*(generalMeanRows 732).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 732).c*(generalMeanRows 732).criticalPoint j.val)).2-
      (generalMeanRows 732).J/2-(generalMeanRows 732).error (generalMeanGrid j.val)+
      (generalMeanRows 732).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 732).c)).2-
      (generalMeanRows 732).J/2-(generalMeanRows 732).error 4 := by
  have he : (generalMeanRows 732).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 732) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 732)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0732

/-! Kernel-checked entropy margins for general spectral rectangle 733. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0733
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5247884104, 5080893814, 4921210779, 4768417502, 4622126114, 4481975781, 4347630395, 4218776510, 4095121477, 3976391781, 3862331530, 3752701091, 3647275856, 3545845115, 3448211036, 3354187732, 3263600408, 3176284580, 3092085362, 3010856805, 2932461295, 2856769000, 2783657350, 2713010567, 2644719230, 2578679862, 2514794562, 2452970653, 2393120359, 2335160506, 2279012239, 2224600768, 2171855120, 2120707916, 2071095159, 2022956040, 1976232749, 1930870308, 1886816407, 1844021257, 1802437444, 1762019801, 1722725283, 1684512849, 1647343356, 1611179454, 1575985489, 1541727416, 1508372711, 1475890293, 1444250446, 1413424749, 1383386012, 1354108209, 1325566419, 1297736773, 1270596401, 1244123376, 1218296676, 1193096133, 1168502394, 1144496879, 1121061746, 1098179855, 1075834733, 1054010545, 1032692061, 1011864629, 991514149, 971627044, 952190243, 933191149, 914617624, 896457966, 878700891, 861335512, 844351323, 827738182, 811486295, 795586203, 780028765, 764805144, 749906799, 735325465, 721053150, 707082117, 693404875, 680014174, 666902987, 654064509, 641492143, 629179492, 617120355, 605308717, 593738741, 582404760, 571301278, 560422952, 549764598, 539321176, 529087790, 519059681, 509232222, 499600915, 490161382, 480909367, 471840726, 462951428, 454237547, 445695261, 437320848, 429110682, 421061230, 413169050, 405430787, 397843170, 390403012, 383107201, 375952706, 368936567, 362055899]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 733).prefactor = (2297749990608629/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 733).cutoff/(generalMeanRows 733).c)).2 =
    (411031435767121/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 733).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 733).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 733).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 733

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 733).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 733).criticalRate j.val*(generalMeanRows 733).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 733).c*(generalMeanRows 733).criticalPoint j.val)).2-
      (generalMeanRows 733).J/2-(generalMeanRows 733).error (generalMeanGrid j.val)+
      (generalMeanRows 733).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 733).c)).2-
      (generalMeanRows 733).J/2-(generalMeanRows 733).error 4 := by
  have he : (generalMeanRows 733).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 733) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 733)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0733

/-! Kernel-checked entropy margins for general spectral rectangle 734. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0734
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5265766644, 5098207323, 4937980156, 4784666226, 4637876339, 4497248433, 4362445257, 4233152292, 4109075896, 3989941620, 3875492701, 3765488688, 3659704209, 3557927835, 3459961061, 3365617366, 3274721360, 3187107997, 3102621864, 3021116514, 2942453867, 2866503644, 2793142861, 2722255345, 2653731299, 2587466898, 2523363904, 2461329326, 2401275088, 2343117732, 2286778136, 2232181254, 2179255871, 2127934380, 2078152564, 2029849407, 1982966903, 1937449886, 1893245869, 1850304891, 1808579378, 1768024010, 1728595593, 1690252947, 1652956797, 1616669663, 1581355772, 1546980962, 1513512599, 1480919495, 1449171832, 1418241095, 1388099999, 1358722429, 1330083381, 1302158904, 1274926049, 1248362816, 1222448109, 1197161694, 1172484149, 1148396833, 1124881844, 1101921981, 1079500717, 1057602162, 1036211033, 1015312630, 994892804, 974937933, 955434899, 936371064, 917734249, 899512711, 881695127, 864270574, 847228510, 830558759, 814251493, 798297220, 782686769, 767411273, 752462160, 737831140, 723510190, 709491549, 695767702, 682331371, 669175507, 656293281, 643678073, 631323466, 619223237, 607371350, 595761948, 584389346, 573248027, 562332633, 551637960, 541158951, 530890694, 520828414, 510967468, 501303341, 491831642, 482548100, 473448557, 464528968, 455785394, 447214000, 438811050, 430572907, 422496026, 414576953, 406812321, 399198849, 391733338, 384412666, 377233791, 370193745, 363289630]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 734).prefactor = (2305579737906931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 734).cutoff/(generalMeanRows 734).c)).2 =
    (411031435767121/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 734).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 734).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 734).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 734

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 734).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 734).criticalRate j.val*(generalMeanRows 734).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 734).c*(generalMeanRows 734).criticalPoint j.val)).2-
      (generalMeanRows 734).J/2-(generalMeanRows 734).error (generalMeanGrid j.val)+
      (generalMeanRows 734).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 734).c)).2-
      (generalMeanRows 734).J/2-(generalMeanRows 734).error 4 := by
  have he : (generalMeanRows 734).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 734) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 734)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0734

/-! Kernel-checked entropy margins for general spectral rectangle 735. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0735
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5198071306, 5030211937, 4869710010, 4716146562, 4569132289, 4428304957, 4293327092, 4163883905, 4039681440, 3920444897, 3805917128, 3695857269, 3590039506, 3488251950, 3390295613, 3295983478, 3205139641, 3117598537, 3033204219, 2951809704, 2873276367, 2797473383, 2724277219, 2653571155, 2585244847, 2519193921, 2455319601, 2393528355, 2333731576, 2275845277, 2219789816, 2165489633, 2112873007, 2061871831, 2012421401, 1964460218, 1917929804, 1872774530, 1828941457, 1786380180, 1745042691, 1704883246, 1665858238, 1627926083, 1591047110, 1555183459, 1520298982, 1486359152, 1453330982, 1421182939, 1389884874, 1359407943, 1329724548, 1300808268, 1272633803, 1245176914, 1218414373, 1192323911, 1166884172, 1142074667, 1117875733, 1094268491, 1071234810, 1048757272, 1026819136, 1005404306, 984497303, 964083236, 944147772, 924677113, 905657971, 887077543, 868923495, 851183931, 833847385, 816902792, 800339478, 784147139, 768315824, 752835924, 737698154, 722893541, 708413411, 694249373, 680393314, 666837381, 653573975, 640595737, 627895542, 615466487, 603301884, 591395248, 579740297, 568330933, 557161246, 546225498, 535518123, 525033717, 514767031, 504712971, 494866584, 485223061, 475777726, 466526035, 457463569, 448586029, 439889237, 431369123, 423021732, 414843209, 406829806, 398977869, 391283843, 383744263, 376355755, 369115029, 362018881, 355064187, 348247901, 341567052, 335018746]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 735).prefactor = (4614644461042061/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 735).cutoff/(generalMeanRows 735).c)).2 =
    (400743559416903/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 735).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 735).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 735).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 735

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 735).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 735).criticalRate j.val*(generalMeanRows 735).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 735).c*(generalMeanRows 735).criticalPoint j.val)).2-
      (generalMeanRows 735).J/2-(generalMeanRows 735).error (generalMeanGrid j.val)+
      (generalMeanRows 735).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 735).c)).2-
      (generalMeanRows 735).J/2-(generalMeanRows 735).error 4 := by
  have he : (generalMeanRows 735).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 735) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 735)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0735

/-! Kernel-checked entropy margins for general spectral rectangle 736. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0736
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5129978602, 4961903523, 4801221521, 4647512017, 4500384177, 4359474319, 4224443586, 4094975877, 3970775985, 3851567918, 3737093386, 3627110437, 3521392214, 3419725829, 3321911337, 3227760802, 3137097440, 3049754838, 2965576235, 2884413866, 2806128351, 2730588144, 2657669012, 2587253561, 2519230801, 2453495733, 2389948978, 2328496425, 2269048904, 2211521889, 2155835215, 2101912820, 2049682495, 1999075664, 1950027171, 1902475078, 1856360485, 1811627355, 1768222354, 1726094698, 1685196011, 1645480193, 1606903295, 1569423403, 1533000527, 1497596497, 1463174868, 1429700827, 1397141109, 1365463913, 1334638832, 1304636775, 1275429902, 1246991562, 1219296230, 1192319454, 1166037798, 1140428794, 1115470894, 1091143423, 1067426539, 1044301194, 1021749092, 999752655, 978294990, 957359855, 936931632, 916995291, 897536373, 878540954, 859995628, 841887477, 824204057, 806933370, 790063847, 773584329, 757484050, 741752617, 726379999, 711356506, 696672777, 682319767, 668288734, 654571222, 641159056, 628044325, 615219375, 602676793, 590409407, 578410266, 566672638, 555189999, 543956025, 532964586, 522209735, 511685705, 501386900, 491307889, 481443400, 471788313, 462337658, 453086605, 444030462, 435164670, 426484795, 417986528, 409665680, 401518174, 393540045, 385727436, 378076590, 370583855, 363245671, 356058574, 349019191, 342124233, 335370500, 328754871, 322274306, 315925841, 309706587]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 736).prefactor = (115762503666451/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 736).cutoff/(generalMeanRows 736).c)).2 =
    (49163572616173/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 736).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 736).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 736).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 736

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 736).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 736).criticalRate j.val*(generalMeanRows 736).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 736).c*(generalMeanRows 736).criticalPoint j.val)).2-
      (generalMeanRows 736).J/2-(generalMeanRows 736).error (generalMeanGrid j.val)+
      (generalMeanRows 736).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 736).c)).2-
      (generalMeanRows 736).J/2-(generalMeanRows 736).error 4 := by
  have he : (generalMeanRows 736).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 736) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 736)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0736

/-! Kernel-checked entropy margins for general spectral rectangle 737. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0737
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5002889358, 4834390394, 4673332916, 4519296089, 4371888711, 4230746622, 4095530401, 3965923294, 3841629369, 3722371842, 3607891575, 3497945719, 3392306472, 3290759968, 3193105251, 3099153350, 3008726421, 2921656978, 2837787174, 2756968148, 2679059420, 2603928341, 2531449576, 2461504633, 2393981428, 2328773877, 2265781525, 2204909195, 2146066667, 2089168377, 2034133137, 1980883877, 1929347401, 1879454161, 1831138048, 1784336191, 1738988777, 1695038876, 1652432279, 1611117350, 1571044882, 1532167963, 1494441856, 1457823876, 1422273285, 1387751186, 1354220428, 1321645511, 1289992504, 1259228962, 1229323850, 1200247472, 1171971401, 1144468418, 1117712450, 1091678512, 1066342658, 1041681923, 1017674282, 994298601, 971534593, 949362783, 927764462, 906721658, 886217096, 866234169, 846756907, 827769944, 809258495, 791208329, 773605739, 756437527, 739690974, 723353823, 707414256, 691860877, 676682695, 661869101, 647409857, 633295081, 619515225, 606061070, 592923705, 580094518, 567565184, 555327652, 543374133, 531697093, 520289237, 509143508, 498253070, 487611302, 477211790, 467048321, 457114870, 447405599, 437914847, 428637120, 419567094, 410699598, 402029616, 393552280, 385262860, 377156766, 369229539, 361476845, 353894477, 346478341, 339224462, 332128972, 325188113, 318398228, 311755760, 305257249, 298899327, 292678717, 286592230, 280636760, 274809284, 269106858, 263526613]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 737).prefactor = (1159456169529859/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 737).cutoff/(generalMeanRows 737).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 737).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 737).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 737).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 737

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 737).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 737).criticalRate j.val*(generalMeanRows 737).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 737).c*(generalMeanRows 737).criticalPoint j.val)).2-
      (generalMeanRows 737).J/2-(generalMeanRows 737).error (generalMeanGrid j.val)+
      (generalMeanRows 737).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 737).c)).2-
      (generalMeanRows 737).J/2-(generalMeanRows 737).error 4 := by
  have he : (generalMeanRows 737).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 737) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 737)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0737

/-! Kernel-checked entropy margins for general spectral rectangle 738. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0738
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5149874540, 4981172367, 4819877900, 4665570647, 4517859822, 4376381744, 4240797526, 4110790999, 3986066860, 3866348993, 3751378960, 3640914640, 3534728986, 3432608905, 3334354232, 3239776797, 3148699574, 3060955895, 2976388740, 2894850077, 2816200255, 2740307452, 2667047156, 2596301697, 2527959801, 2461916192, 2398071209, 2336330463, 2276604510, 2218808549, 2162862146, 2108688968, 2056216547, 2005376045, 1956102051, 1908332377, 1862007878, 1817072275, 1773471997, 1731156031, 1690075774, 1650184908, 1611439267, 1573796729, 1537217098, 1501662006, 1467094815, 1433480523, 1400785682, 1368978315, 1338027840, 1307905000, 1278581792, 1250031407, 1222228169, 1195147476, 1168765750, 1143060383, 1118009693, 1093592876, 1069789965, 1046581788, 1023949933, 1001876708, 980345110, 959338793, 938842034, 918839708, 899317257, 880260667, 861656442, 843491580, 825753554, 808430286, 791510131, 774981857, 758834624, 743057974, 727641807, 712576370, 697852242, 683460319, 669391800, 655638178, 642191222, 629042972, 616185724, 603612022, 591314644, 579286598, 567521110, 556011616, 544751754, 533735356, 522956440, 512409204, 502088020, 491987424, 482102115, 472426943, 462956910, 453687159, 444612972, 435729764, 427033080, 418518586, 410182070, 402019434, 394026695, 386199973, 378535495, 371029588, 363678678, 356479282, 349428011, 342521562, 335756718, 329130346, 322639391, 316280876, 310051899]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 738).prefactor = (2317075214562879/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 738).cutoff/(generalMeanRows 738).c)).2 =
    (97629794710451/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 738).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 738).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 738).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 738

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 738).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 738).criticalRate j.val*(generalMeanRows 738).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 738).c*(generalMeanRows 738).criticalPoint j.val)).2-
      (generalMeanRows 738).J/2-(generalMeanRows 738).error (generalMeanGrid j.val)+
      (generalMeanRows 738).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 738).c)).2-
      (generalMeanRows 738).J/2-(generalMeanRows 738).error 4 := by
  have he : (generalMeanRows 738).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 738) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 738)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0738

/-! Kernel-checked entropy margins for general spectral rectangle 739. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0739
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5083163178, 4914274721, 4752829569, 4598405570, 4450610362, 4309078773, 4173470497, 4043468018, 3918774748, 3799113347, 3684224209, 3573864097, 3467804897, 3365832495, 3267745747, 3173355547, 3082483967, 2994963480, 2910636236, 2829353406, 2750974576, 2675367186, 2602406020, 2531972722, 2463955368, 2398248046, 2334750491, 2273367726, 2214009742, 2156591197, 2101031130, 2047252705, 1995182964, 1944752603, 1895895754, 1848549794, 1802655156, 1758155156, 1714995831, 1673125788, 1632496063, 1593059983, 1554773047, 1517592803, 1481478743, 1446392194, 1412296225, 1379155554, 1346936460, 1315606706, 1285135456, 1255493212, 1226651737, 1198583997, 1171264100, 1144667236, 1118769626, 1093548471, 1068981903, 1045048941, 1021729446, 999004085, 976854285, 955262206, 934210700, 913683281, 893664093, 874137885, 855089976, 836506237, 818373060, 800677336, 783406437, 766548188, 750090851, 734023105, 718334030, 703013084, 688050094, 673435234, 659159015, 645212269, 631586133, 618272043, 605261713, 592547133, 580120550, 567974461, 556101605, 544494948, 533147681, 522053204, 511205124, 500597243, 490223553, 480078226, 470155612, 460450227, 450956750, 441670017, 432585013, 423696869, 415000856, 406492380, 398166977, 390020309, 382048158, 374246423, 366611119, 359138365, 351824391, 344665526, 337658196, 330798926, 324084331, 317511116, 311076071, 304776071, 298608071, 292569105, 286656282]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 739).prefactor = (465020657159403/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 739).cutoff/(generalMeanRows 739).c)).2 =
    (47892383943023/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 739).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 739).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 739).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 739

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 739).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 739).criticalRate j.val*(generalMeanRows 739).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 739).c*(generalMeanRows 739).criticalPoint j.val)).2-
      (generalMeanRows 739).J/2-(generalMeanRows 739).error (generalMeanGrid j.val)+
      (generalMeanRows 739).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 739).c)).2-
      (generalMeanRows 739).J/2-(generalMeanRows 739).error 4 := by
  have he : (generalMeanRows 739).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 739) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 739)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0739

/-! Kernel-checked entropy margins for general spectral rectangle 740. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0740
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5103268992, 4933748692, 4771686424, 4616660117, 4468277448, 4326173240, 4190007150, 4059461592, 3934239878, 3814064540, 3698675823, 3587830316, 3481299718, 3378869705, 3280338915, 3185518006, 3094228808, 3006303539, 2921584090, 2839921365, 2761174679, 2685211197, 2611905424, 2541138727, 2472798900, 2406779754, 2342980742, 2281306611, 2221667077, 2163976522, 2108153716, 2054121557, 2001806823, 1951139950, 1902054816, 1854488547, 1808381330, 1763676239, 1720319077, 1678258219, 1637444475, 1597830952, 1559372933, 1522027757, 1485754711, 1450514922, 1416271267, 1382988273, 1350632037, 1319170142, 1288571581, 1258806686, 1229847059, 1201665506, 1174235981, 1147533527, 1121534220, 1096215122, 1071554229, 1047530431, 1024123461, 1001313862, 979082947, 957412759, 936286040, 915686197, 895597272, 876003912, 856891343, 838245341, 820052210, 802298754, 784972261, 768060477, 751551586, 735434193, 719697304, 704330310, 689322971, 674665395, 660348033, 646361655, 632697343, 619346475, 606300715, 593551998, 581092524, 568914743, 557011346, 545375258, 533999624, 522877806, 512003371, 501370084, 490971899, 480802956, 470857569, 461130223, 451615565, 442308402, 433203690, 424296533, 415582176, 407055999, 398713513, 390550357, 382562290, 374745190, 367095051, 359607973, 352280164, 345107937, 338087699, 331215959, 324489315, 317904455, 311458156, 305147277, 298968759, 292919624, 286996967]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 740).prefactor = (930805814042343/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 740).cutoff/(generalMeanRows 740).c)).2 =
    (190178714291153/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 740).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 740).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 740).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 740

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 740).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 740).criticalRate j.val*(generalMeanRows 740).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 740).c*(generalMeanRows 740).criticalPoint j.val)).2-
      (generalMeanRows 740).J/2-(generalMeanRows 740).error (generalMeanGrid j.val)+
      (generalMeanRows 740).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 740).c)).2-
      (generalMeanRows 740).J/2-(generalMeanRows 740).error 4 := by
  have he : (generalMeanRows 740).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 740) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 740)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0740

/-! Kernel-checked entropy margins for general spectral rectangle 741. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0741
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5037910262, 4868231783, 4706046880, 4550931775, 4402492525, 4260362422, 4124199669, 3993685295, 3868521295, 3748428949, 3633147306, 3522431813, 3416053077, 3313795734, 3215457421, 3120847843, 3029787914, 2942108973, 2857652069, 2776267299, 2697813200, 2622156193, 2549170066, 2478735499, 2410739622, 2345075610, 2281642303, 2220343859, 2161089425, 2103792839, 2048372345, 1994750332, 1942853094, 1892610595, 1843956262, 1796826787, 1751161935, 1706904378, 1663999529, 1622395390, 1582042409, 1542893347, 1504903151, 1468028840, 1432229391, 1397465633, 1363700154, 1330897208, 1299022626, 1268043735, 1237929284, 1208649367, 1180175360, 1152479852, 1125536589, 1099320410, 1073807201, 1048973838, 1024798140, 1001258826, 978335467, 956008451, 934258939, 913068832, 892420736, 872297926, 852684320, 833564446, 814923415, 796746894, 779021085, 761732693, 744868912, 728417398, 712366252, 696703997, 681419565, 666502274, 651941814, 637728232, 623851916, 610303580, 597074251, 584155259, 571538218, 559215021, 547177826, 535419044, 523931333, 512707582, 501740909, 491024647, 480552337, 470317722, 460314736, 450537499, 440980310, 431637638, 422504120, 413574551, 404843878, 396307199, 387959752, 379796915, 371814196, 364007232, 356371786, 348903736, 341599079, 334453920, 327464474, 320627059, 313938093, 307394091, 300991663, 294727508, 288598415, 282601256, 276732987, 270990642, 265371335]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 741).prefactor = (1167572519966327/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 741).cutoff/(generalMeanRows 741).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 741).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 741).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 741).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 741

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 741).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 741).criticalRate j.val*(generalMeanRows 741).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 741).c*(generalMeanRows 741).criticalPoint j.val)).2-
      (generalMeanRows 741).J/2-(generalMeanRows 741).error (generalMeanGrid j.val)+
      (generalMeanRows 741).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 741).c)).2-
      (generalMeanRows 741).J/2-(generalMeanRows 741).error 4 := by
  have he : (generalMeanRows 741).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 741) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 741)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0741

/-! Kernel-checked entropy margins for general spectral rectangle 742. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0742
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5196026247, 5028219589, 4867780854, 4714289550, 4567354997, 4426613717, 4291727112, 4162379386, 4038275672, 3919140357, 3804715564, 3694759776, 3589046600, 3487363628, 3389511416, 3295302543, 3204560750, 3117120163, 3032824564, 2951526737, 2873087858, 2797376934, 2724270289, 2653651086, 2585408888, 2519439248, 2455643332, 2393927570, 2334203330, 2276386615, 2220397783, 2166161284, 2113605418, 2062662107, 2013266681, 1965357685, 1918876688, 1873768114, 1829979077, 1787459235, 1746160642, 1706037617, 1667046622, 1629146141, 1592296572, 1556460124, 1521600721, 1487683906, 1454676764, 1422547831, 1391267028, 1360805580, 1331135958, 1302231809, 1274067898, 1246620052, 1219865106, 1193780855, 1168346004, 1143540124, 1119343608, 1095737637, 1072704134, 1050225734, 1028285748, 1006868133, 985957457, 965538877, 945598105, 926121389, 907095483, 888507627, 870345524, 852597319, 835251581, 818297282, 801723782, 785520809, 769678446, 754187112, 739037552, 724220821, 709728270, 695551536, 681682529, 668113421, 654836632, 641844827, 629130901, 616687969, 604509363, 592588615, 580919458, 569495814, 558311783, 547361645, 536639846, 526140995, 515859855, 505791344, 495930519, 486272582, 476812867, 467546838, 458470085, 449578317, 440867363, 432333163, 423971764, 415779320, 407752088, 399886420, 392178765, 384625663, 377223745, 369969724, 362860400, 355892652, 349063437, 342369788, 335808811]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 742).prefactor = (4626872331257389/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 742).cutoff/(generalMeanRows 742).c)).2 =
    (403540764037963/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 742).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 742).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 742).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 742

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 742).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 742).criticalRate j.val*(generalMeanRows 742).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 742).c*(generalMeanRows 742).criticalPoint j.val)).2-
      (generalMeanRows 742).J/2-(generalMeanRows 742).error (generalMeanGrid j.val)+
      (generalMeanRows 742).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 742).c)).2-
      (generalMeanRows 742).J/2-(generalMeanRows 742).error 4 := by
  have he : (generalMeanRows 742).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 742) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 742)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0742

/-! Kernel-checked entropy margins for general spectral rectangle 743. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0743
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5301714740, 5133011532, 4971690534, 4817329967, 4669537982, 4527950044, 4392226599, 4262050984, 4137127548, 4017179972, 3901949738, 3791194755, 3684688111, 3582216935, 3483581366, 3388593610, 3297077078, 3208865601, 3123802701, 3041740935, 2962541277, 2886072561, 2812210961, 2740839513, 2671847671, 2605130899, 2540590290, 2478132217, 2417668003, 2359113621, 2302389409, 2247419807, 2194133116, 2142461265, 2092339601, 2043706691, 1996504131, 1950676381, 1906170594, 1862936468, 1820926106, 1780093876, 1740396290, 1701791889, 1664241127, 1627706270, 1592151299, 1557541821, 1523844978, 1491029368, 1459064973, 1427923079, 1397576217, 1367998093, 1339163534, 1311048423, 1283629656, 1256885082, 1230793462, 1205334423, 1180488411, 1156236657, 1132561136, 1109444532, 1086870203, 1064822152, 1043284991, 1022243920, 1001684693, 981593595, 961957418, 942763439, 923999395, 905653463, 887714244, 870170737, 853012331, 836228779, 819810188, 803746999, 788029979, 772650201, 757599034, 742868132, 728449417, 714335074, 700517537, 686989479, 673743804, 660773634, 648072305, 635633356, 623450522, 611517725, 599829068, 588378829, 577161451, 566171540, 555403857, 544853310, 534514955, 524383982, 514455717, 504725615, 495189256, 485842337, 476680674, 467700193, 458896929, 450267020, 441806705, 433512322, 425380302, 417407168, 409589529, 401924082, 394407605, 387036957, 379809074, 372720967, 365769719]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 743).prefactor = (464263872937873/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 743).cutoff/(generalMeanRows 743).c)).2 =
    (411031435767121/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 743).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 743).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 743).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 743

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 743).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 743).criticalRate j.val*(generalMeanRows 743).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 743).c*(generalMeanRows 743).criticalPoint j.val)).2-
      (generalMeanRows 743).J/2-(generalMeanRows 743).error (generalMeanGrid j.val)+
      (generalMeanRows 743).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 743).c)).2-
      (generalMeanRows 743).J/2-(generalMeanRows 743).error 4 := by
  have he : (generalMeanRows 743).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 743) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 743)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0743

/-! Kernel-checked entropy margins for general spectral rectangle 744. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0744
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5147604950, 4978952373, 4817718276, 4663480633, 4515847270, 4374453253, 4238958561, 4109046008, 3984419371, 3864801711, 3749933850, 3639573006, 3533491540, 3431475835, 3333325257, 3238851226, 3147876349, 3060233642, 2975765806, 2894324566, 2815770067, 2739970307, 2666800628, 2596143234, 2527886751, 2461925821, 2398160723, 2336497021, 2276845241, 2219120566, 2163242556, 2109134886, 2056725101, 2005944388, 1956727366, 1909011886, 1862738846, 1817852016, 1774297877, 1732025472, 1690986259, 1651133980, 1612424534, 1574815863, 1538267840, 1502742163, 1468202263, 1434613207, 1401941615, 1370155579, 1339224584, 1309119441, 1279812215, 1251276162, 1223485670, 1196416203, 1170044245, 1144347250, 1119303595, 1094892536, 1071094163, 1047889361, 1025259771, 1003187755, 981656362, 960649296, 940150881, 920146041, 900620263, 881559577, 862950529, 844780160, 827035981, 809705952, 792778466, 776242326, 760086727, 744301242, 728875804, 713800691, 699066509, 684664183, 670584940, 656820296, 643362046, 630202254, 617333237, 604747561, 592438024, 580397654, 568619696, 557097604, 545825031, 534795825, 524004021, 513443831, 503109640, 492995998, 483097615, 473409354, 463926227, 454643388, 445556128, 436659873, 427950175, 419422709, 411073271, 402897770, 394892229, 387052776, 379375642, 371857162, 364493765, 357281974, 350218403, 343299755, 336522816, 329884457, 323381624, 317011346, 310770723]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 744).prefactor = (4646410311610061/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 744).cutoff/(generalMeanRows 744).c)).2 =
    (49163572616173/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 744).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 744).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 744).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 744

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 744).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 744).criticalRate j.val*(generalMeanRows 744).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 744).c*(generalMeanRows 744).criticalPoint j.val)).2-
      (generalMeanRows 744).J/2-(generalMeanRows 744).error (generalMeanGrid j.val)+
      (generalMeanRows 744).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 744).c)).2-
      (generalMeanRows 744).J/2-(generalMeanRows 744).error 4 := by
  have he : (generalMeanRows 744).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 744) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 744)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0744

/-! Kernel-checked entropy margins for general spectral rectangle 745. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0745
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5165291861, 4996059802, 4834271713, 4679504118, 4531363494, 4389483653, 4253523408, 4123164482, 3998109635, 3878080975, 3762818434, 3652078395, 3545632439, 3443266212, 3344778395, 3249979755, 3158692293, 3070748450, 2985990387, 2904269319, 2825444911, 2749384707, 2675963621, 2605063451, 2536572442, 2470384874, 2406400682, 2344525107, 2284668367, 2226745353, 2170675349, 2116381767, 2063791904, 2012836711, 1963450583, 1915571155, 1869139123, 1824098063, 1780394275, 1737976625, 1696796403, 1656807193, 1617964743, 1580226851, 1543553251, 1507905510, 1473246932, 1439542466, 1406758616, 1374863364, 1343826092, 1313617509, 1284209585, 1255575484, 1227689505, 1200527029, 1174064458, 1148279169, 1123149466, 1098654532, 1074774389, 1051489856, 1028782511, 1006634657, 985029284, 963950038, 943381192, 923307616, 903714748, 884588571, 865915584, 847682782, 829877635, 812488061, 795502413, 778909455, 762698346, 746858623, 731380185, 716253274, 701468466, 687016655, 672889036, 659077097, 645572606, 632367597, 619454363, 606825443, 594473611, 582391871, 570573445, 559011763, 547700458, 536633357, 525804473, 515207999, 504838300, 494689908, 484757514, 475035965, 465520254, 456205519, 447087037, 438160215, 429420590, 420863824, 412485698, 404282107, 396249059, 388382669, 380679158, 373134845, 365746147, 358509577, 351421736, 344479316, 337679092, 331017923, 324492747, 318100581, 311838515]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 745).prefactor = (582796892885799/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 745).cutoff/(generalMeanRows 745).c)).2 =
    (49163572616173/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 745).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 745).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 745).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 745

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 745).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 745).criticalRate j.val*(generalMeanRows 745).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 745).c*(generalMeanRows 745).criticalPoint j.val)).2-
      (generalMeanRows 745).J/2-(generalMeanRows 745).error (generalMeanGrid j.val)+
      (generalMeanRows 745).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 745).c)).2-
      (generalMeanRows 745).J/2-(generalMeanRows 745).error 4 := by
  have he : (generalMeanRows 745).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 745) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 745)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0745

/-! Kernel-checked entropy margins for general spectral rectangle 746. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0746
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5115556521, 4945559692, 4783068114, 4627655195, 4478924484, 4336507041, 4200059085, 4069259896, 3943809926, 3823429102, 3707855292, 3596842923, 3490161721, 3387595573, 3288941486, 3194008638, 3102617516, 3014599119, 2929794235, 2848052770, 2769233137, 2693201689, 2619832198, 2549005373, 2480608417, 2414534612, 2350682939, 2288957726, 2229268313, 2171528755, 2115657530, 2061577281, 2009214563, 1958499618, 1909366161, 1861751174, 1815594724, 1770839787, 1727432082, 1685319919, 1644454057, 1604787566, 1566275701, 1528875785, 1492547099, 1457250772, 1422949688, 1389608391, 1357192997, 1325671116, 1295011771, 1265185325, 1236163416, 1207918892, 1180425745, 1153659062, 1127594961, 1102210551, 1077483871, 1053393857, 1029920290, 1007043757, 984745615, 963007955, 941813561, 921145885, 900989011, 881327630, 862147006, 843432958, 825171825, 807350452, 789956162, 772976736, 756400391, 740215766, 724411898, 708978207, 693904481, 679180858, 664797812, 650746139, 637016945, 623601629, 610491877, 597679643, 585157147, 572916854, 560951473, 549253944, 537817427, 526635296, 515701130, 505008705, 494551988, 484325124, 474322439, 464538424, 454967734, 445605180, 436445726, 427484478, 418716686, 410137733, 401743133, 393528527, 385489675, 377622457, 369922865, 362387001, 355011072, 347791388, 340724357, 333806485, 327034367, 320404689, 313914226, 307559832, 301338446, 295247084, 289282839]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 746).prefactor = (4694469557583017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 746).cutoff/(generalMeanRows 746).c)).2 =
    (4824105920397/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 746).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 746).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 746).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 746

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 746).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 746).criticalRate j.val*(generalMeanRows 746).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 746).c*(generalMeanRows 746).criticalPoint j.val)).2-
      (generalMeanRows 746).J/2-(generalMeanRows 746).error (generalMeanGrid j.val)+
      (generalMeanRows 746).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 746).c)).2-
      (generalMeanRows 746).J/2-(generalMeanRows 746).error 4 := by
  have he : (generalMeanRows 746).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 746) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 746)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0746

/-! Kernel-checked entropy margins for general spectral rectangle 747. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0747
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5100775034, 4931301422, 4769296904, 4614337865, 4466030585, 4324008626, 4187930501, 4057477598, 3932352297, 3812276300, 3696989101, 3586246620, 3479819952, 3377494241, 3279067648, 3184350409, 3093163983, 3005340260, 2920720844, 2839156390, 2760505997, 2684636647, 2611422689, 2540745358, 2472492341, 2406557360, 2342839802, 2281244362, 2221680718, 2164063232, 2108310664, 2054345910, 2002095762, 1951490672, 1902464546, 1854954545, 1808900894, 1764246712, 1720937851, 1678922740, 1638152243, 1598579527, 1560159937, 1522850873, 1486611687, 1451403572, 1417189469, 1383933974, 1351603250, 1320164945, 1289588121, 1259843174, 1230901770, 1202736783, 1175322229, 1148633214, 1122645875, 1097337336, 1072685651, 1048669767, 1025269477, 1002465378, 980238835, 958571945, 937447500, 916848959, 896760410, 877166548, 858052644, 839404517, 821208512, 803451478, 786120739, 769204081, 752689723, 736566307, 720822873, 705448844, 690434011, 675768514, 661442832, 647447764, 633774417, 620414197, 607358790, 594600157, 582130519, 569942347, 558028354, 546381483, 534994901, 523861984, 512976318, 502331684, 491922051, 481741574, 471784581, 462045569, 452519200, 443200290, 434083809, 425164870, 416438728, 407900772, 399546524, 391371629, 383371857, 375543091, 367881332, 360382688, 353043373, 345859703, 338828095, 331945060, 325207200, 318611210, 312153870, 305832041, 299642671, 293582781, 287649472]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 747).prefactor = (186652733779087/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 747).cutoff/(generalMeanRows 747).c)).2 =
    (47892383943023/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 747).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 747).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 747).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 747

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 747).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 747).criticalRate j.val*(generalMeanRows 747).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 747).c*(generalMeanRows 747).criticalPoint j.val)).2-
      (generalMeanRows 747).J/2-(generalMeanRows 747).error (generalMeanGrid j.val)+
      (generalMeanRows 747).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 747).c)).2-
      (generalMeanRows 747).J/2-(generalMeanRows 747).error 4 := by
  have he : (generalMeanRows 747).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 747) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 747)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0747

/-! Kernel-checked entropy margins for general spectral rectangle 748. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0748
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5035108532, 4865481173, 4703358308, 4548314625, 4399954794, 4257910853, 4121839871, 3991421855, 3866357879, 3746368395, 3631191708, 3520582600, 3414311083, 3312161261, 3213930301, 3119427488, 3028473368, 2940898956, 2856545018, 2775261403, 2696906437, 2621346359, 2548454802, 2478112317, 2410205929, 2344628725, 2281279482, 2220062305, 2160886308, 2103665307, 2048317537, 1994765390, 1942935169, 1892756860, 1844163918, 1797093066, 1751484113, 1707279776, 1664425516, 1622869388, 1582561898, 1543455865, 1505506300, 1468670282, 1432906854, 1398176910, 1364443107, 1331669762, 1299822775, 1268869539, 1238778869, 1209520927, 1181067154, 1153390203, 1126463882, 1100263097, 1074763794, 1049942908, 1025778320, 1002248805, 979333992, 957014324, 935271017, 914086023, 893442000, 873322272, 853710807, 834592177, 815951540, 797774608, 780047622, 762757331, 745890967, 729436225, 713381242, 697714578, 682425198, 667502452, 652936064, 638716110, 624833006, 611277495, 598040633, 585113772, 572488553, 560156892, 548110970, 536343219, 524846317, 513613175, 502636928, 491910927, 481428731, 471184098, 461170979, 451383507, 441815996, 432462929, 423318954, 414378879, 405637663, 397090413, 388732378, 380558946, 372565633, 364748087, 357102076, 349623487, 342308324, 335152699, 328152834, 321305050, 314605773, 308051523, 301638914, 295364650, 289225523, 283218411, 277340272, 271588143, 265959141]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 748).prefactor = (4682485940520311/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 748).cutoff/(generalMeanRows 748).c)).2 =
    (375813031452109/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 748).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 748).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 748).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 748

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 748).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 748).criticalRate j.val*(generalMeanRows 748).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 748).c*(generalMeanRows 748).criticalPoint j.val)).2-
      (generalMeanRows 748).J/2-(generalMeanRows 748).error (generalMeanGrid j.val)+
      (generalMeanRows 748).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 748).c)).2-
      (generalMeanRows 748).J/2-(generalMeanRows 748).error 4 := by
  have he : (generalMeanRows 748).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 748) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 748)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0748

/-! Kernel-checked entropy margins for general spectral rectangle 749. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0749
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5055512538, 4885241209, 4722489638, 4566832566, 4417874675, 4275247975, 4138609474, 4007639087, 3882037769, 3761525825, 3645841391, 3534739063, 3427988643, 3325374017, 3226692114, 3131751973, 3040373883, 2952388595, 2867636602, 2785967476, 2707239262, 2631317912, 2558076775, 2487396112, 2419162660, 2353269220, 2289614279, 2228101660, 2168640193, 2111143415, 2055529284, 2001719918, 1949641353, 1899223308, 1850398979, 1803104834, 1757280431, 1712868240, 1669813484, 1628063981, 1587570008, 1548284160, 1510161228, 1473158080, 1437233548, 1402348327, 1368464873, 1335547315, 1303561364, 1272474235, 1242254564, 1212872344, 1184298850, 1156506575, 1129469173, 1103161396, 1077559045, 1052638915, 1028378748, 1004757188, 981753736, 959348710, 937523206, 916259062, 895538822, 875345704, 855663568, 836476890, 817770728, 799530699, 781742956, 764394159, 747471457, 730962462, 714855234, 699138256, 683800421, 668831009, 654219675, 639956432, 626031632, 612435958, 599160407, 586196276, 573535152, 561168898, 549089645, 537289779, 525761930, 514498964, 503493974, 492740269, 482231370, 471960995, 461923059, 452111661, 442521079, 433145765, 423980335, 415019565, 406258388, 397691882, 389315270, 381123911, 373113301, 365279061, 357616936, 350122793, 342792614, 335622490, 328608623, 321747318, 315034981, 308468115, 302043317, 295757275, 289606767, 283588654, 277699882, 271937474, 266298533]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 749).prefactor = (4686607904899937/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 749).cutoff/(generalMeanRows 749).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 749).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 749).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 749).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 749

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 749).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 749).criticalRate j.val*(generalMeanRows 749).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 749).c*(generalMeanRows 749).criticalPoint j.val)).2-
      (generalMeanRows 749).J/2-(generalMeanRows 749).error (generalMeanGrid j.val)+
      (generalMeanRows 749).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 749).c)).2-
      (generalMeanRows 749).J/2-(generalMeanRows 749).error 4 := by
  have he : (generalMeanRows 749).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 749) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 749)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0749

/-! Kernel-checked entropy margins for general spectral rectangle 750. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0750
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4991173169, 4820775105, 4657932120, 4502217211, 4353233408, 4210611158, 4074005985, 3943096396, 3817582002, 3697181832, 3581632807, 3470688360, 3364117186, 3261702111, 3163239052, 3068536080, 2977412554, 2889698338, 2805233072, 2723865513, 2645452920, 2569860495, 2496960864, 2426633595, 2358764759, 2293246518, 2229976743, 2168858666, 2109800549, 2052715382, 1997520599, 1944137812, 1892492570, 1842514126, 1794135226, 1747291906, 1701923307, 1657971501, 1615381323, 1574100225, 1534078126, 1495267280, 1457622149, 1421099284, 1385657215, 1351256344, 1317858848, 1285428586, 1253931010, 1223333086, 1193603216, 1164711160, 1136627976, 1109325946, 1082778523, 1056960266, 1031846791, 1007414716, 983641614, 960505966, 937987120, 916065245, 894721295, 873936974, 853694697, 833977559, 814769305, 796054297, 777817490, 760044399, 742721082, 725834108, 709370540, 693317910, 677664201, 662397824, 647507602, 632982753, 618812870, 604987909, 591498171, 578334287, 565487209, 552948190, 540708778, 528760799, 517096350, 505707786, 494587707, 483728955, 473124598, 462767927, 452652440, 442771842, 433120032, 423691098, 414479307, 405479103, 396685095, 388092056, 379694915, 371488748, 363468779, 355630370, 347969018, 340480350, 333160117, 326004193, 319008567, 312169343, 305482731, 298945048, 292552714, 286302244, 280190251, 274213440, 268368603, 262652619, 257062452, 251595144, 246247818]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 750).prefactor = (2351491371913243/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 750).cutoff/(generalMeanRows 750).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 750).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 750).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 750).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 750

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 750).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 750).criticalRate j.val*(generalMeanRows 750).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 750).c*(generalMeanRows 750).criticalPoint j.val)).2-
      (generalMeanRows 750).J/2-(generalMeanRows 750).error (generalMeanGrid j.val)+
      (generalMeanRows 750).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 750).c)).2-
      (generalMeanRows 750).J/2-(generalMeanRows 750).error 4 := by
  have he : (generalMeanRows 750).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 750) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 750)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0750

/-! Kernel-checked entropy margins for general spectral rectangle 751. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0751
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4945274834, 4774185171, 4610712054, 4454425207, 4304924593, 4161837773, 4024817554, 3893539885, 3767701964, 3647020539, 3531230374, 3420082863, 3313344768, 3210797080, 3112233979, 3017461882, 2926298580, 2838572443, 2754121690, 2672793725, 2594444519, 2518938046, 2446145759, 2375946109, 2308224101, 2242870876, 2179783334, 2118863776, 2060019576, 2003162874, 1948210291, 1895082662, 1843704793, 1794005225, 1745916022, 1699372569, 1654313382, 1610679935, 1568416492, 1527469955, 1487789719, 1449327535, 1412037383, 1375875353, 1340799533, 1306769901, 1273748230, 1241697989, 1210584260, 1180373653, 1151034227, 1122535418, 1094847970, 1067943867, 1041796275, 1016379481, 991668838, 967640713, 944272441, 921542274, 899429340, 877913600, 856975809, 836597480, 816760846, 797448830, 778645011, 760333593, 742499381, 725127749, 708204617, 691716426, 675650115, 659993101, 644733255, 629858883, 615358710, 601221858, 587437832, 573996503, 560888094, 548103160, 535632582, 523467549, 511599544, 500020337, 488721968, 477696743, 466937214, 456436179, 446186665, 436181923, 426415420, 416880827, 407572014, 398483040, 389608152, 380941769, 372478483, 364213048, 356140378, 348255538, 340553739, 333030336, 325680816, 318500802, 311486042, 304632407, 297935886, 291392581, 284998708, 278750585, 272644637, 266677386, 260845452, 255145547, 249574474, 244129121, 238806464, 233603558, 228517537]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 751).prefactor = (591988032608661/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 751).cutoff/(generalMeanRows 751).c)).2 =
    (179269190593833/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 751).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 751).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 751).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 751

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 751).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 751).criticalRate j.val*(generalMeanRows 751).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 751).c*(generalMeanRows 751).criticalPoint j.val)).2-
      (generalMeanRows 751).J/2-(generalMeanRows 751).error (generalMeanGrid j.val)+
      (generalMeanRows 751).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 751).c)).2-
      (generalMeanRows 751).J/2-(generalMeanRows 751).error 4 := by
  have he : (generalMeanRows 751).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 751) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 751)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0751

/-! Kernel-checked entropy margins for general spectral rectangle 752. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0752
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5275739943, 5101656097, 4935265674, 4776130194, 4623842193, 4478022521, 4338317922, 4204398871, 4075957633, 3952706513, 3834376282, 3720714748, 3611485467, 3506466563, 3405449660, 3308238909, 3214650093, 3124509813, 3037654738, 2953930921, 2873193161, 2795304425, 2720135314, 2647563559, 2577473570, 2509756008, 2444307395, 2381029745, 2319830229, 2260620861, 2203318202, 2147843090, 2094120384, 2042078733, 1991650346, 1942770795, 1895378815, 1849416129, 1804827274, 1761559450, 1719562364, 1678788099, 1639190977, 1600727443, 1563355945, 1527036832, 1491732246, 1457406033, 1424023649, 1391552081, 1359959760, 1329216494, 1299293393, 1270162804, 1241798248, 1214174363, 1187266845, 1161052397, 1135508681, 1110614268, 1086348596, 1062691927, 1039625308, 1017130533, 995190108, 973787217, 952905690, 932529975, 912645108, 893236683, 874290832, 855794198, 837733911, 820097568, 802873211, 786049310, 769614739, 753558763, 737871021, 722541507, 707560557, 692918835, 678607318, 664617281, 650940290, 637568186, 624493075, 611707315, 599203511, 586974501, 575013346, 563313325, 551867924, 540670830, 529715918, 518997252, 508509072, 498245787, 488201972, 478372363, 468751844, 459335450, 450118355, 441095872, 432263444, 423616643, 415151163, 406862816, 398747529, 390801340, 383020393, 375400936, 367939315, 360631976, 353475454, 346466378, 339601463, 332877507, 326291393, 319840081, 313520609]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 752).prefactor = (958757930237053/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 752).cutoff/(generalMeanRows 752).c)).2 =
    (392187457384243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 752).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 752).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 752).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 752

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 752).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 752).criticalRate j.val*(generalMeanRows 752).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 752).c*(generalMeanRows 752).criticalPoint j.val)).2-
      (generalMeanRows 752).J/2-(generalMeanRows 752).error (generalMeanGrid j.val)+
      (generalMeanRows 752).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 752).c)).2-
      (generalMeanRows 752).J/2-(generalMeanRows 752).error 4 := by
  have he : (generalMeanRows 752).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 752) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 752)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0752

/-! Kernel-checked entropy margins for general spectral rectangle 753. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0753
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5493155527, 5317130300, 5148830447, 4987814765, 4833673321, 4686024727, 4544513694, 4408808859, 4278600819, 4153600371, 4033536922, 3918157050, 3807223198, 3700512491, 3597815655, 3498936036, 3403688695, 3311899593, 3223404828, 3138049945, 3055689300, 2976185471, 2899408716, 2825236474, 2753552904, 2684248452, 2617219463, 2552367805, 2489600532, 2428829567, 2369971404, 2312946837, 2257680702, 2204101637, 2152141863, 2101736973, 2052825740, 2005349932, 1959254146, 1914485646, 1870994215, 1828732014, 1787653456, 1747715073, 1708875413, 1671094920, 1634335841, 1598562124, 1563739332, 1529834557, 1496816337, 1464654589, 1433320527, 1402786605, 1373026450, 1344014802, 1315727460, 1288141228, 1261233864, 1234984036, 1209371275, 1184375935, 1159979150, 1136162799, 1112909471, 1090202429, 1068025581, 1046363445, 1025201128, 1004524291, 984319128, 964572344, 945271123, 926403117, 907956418, 889919541, 872281404, 855031312, 838158941, 821654319, 805507811, 789710109, 774252212, 759125419, 744321313, 729831749, 715648845, 701764969, 688172732, 674864975, 661834760, 649075366, 636580273, 624343160, 612357895, 600618530, 589119288, 577854566, 566818919, 556007060, 545413853, 535034306, 524863569, 514896923, 505129784, 495557689, 486176299, 476981390, 467968852, 459134684, 450474990, 441985975, 433663944, 425505296, 417506523, 409664204, 401975007, 394435682, 387043060, 379794050, 372685637]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 753).prefactor = (603360695062631/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 753).cutoff/(generalMeanRows 753).c)).2 =
    (203641041803363/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 753).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 753).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 753).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 753

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 753).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 753).criticalRate j.val*(generalMeanRows 753).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 753).c*(generalMeanRows 753).criticalPoint j.val)).2-
      (generalMeanRows 753).J/2-(generalMeanRows 753).error (generalMeanGrid j.val)+
      (generalMeanRows 753).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 753).c)).2-
      (generalMeanRows 753).J/2-(generalMeanRows 753).error 4 := by
  have he : (generalMeanRows 753).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 753) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 753)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0753

/-! Kernel-checked entropy margins for general spectral rectangle 754. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0754
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5098644306, 4923335422, 4755835319, 4595701829, 4442523896, 4295918860, 4155530034, 4021024543, 3892091372, 3768439621, 3649796924, 3535908022, 3426533468, 3321448452, 3220441727, 3123314637, 3029880224, 2939962409, 2853395243, 2770022222, 2689695651, 2612276064, 2537631685, 2465637932, 2396176958, 2329137226, 2264413117, 2201904560, 2141516700, 2083159575, 2026747828, 1972200433, 1919440438, 1868394729, 1818993808, 1771171588, 1724865194, 1680014788, 1636563396, 1594456748, 1553643132, 1514073254, 1475700106, 1438478841, 1402366661, 1367322709, 1333307960, 1300285134, 1268218600, 1237074290, 1206819624, 1177423430, 1148855872, 1121088389, 1094093624, 1067845368, 1042318504, 1017488952, 993333618, 969830349, 946957884, 924695817, 903024550, 881925260, 861379859, 841370963, 821881856, 802896465, 784399324, 766375549, 748810815, 731691326, 715003796, 698735420, 682873863, 667407228, 652324046, 637613254, 623264176, 609266510, 595610311, 582285974, 569284223, 556596096, 544212931, 532126356, 520328275, 508810859, 497566534, 486587971, 475868078, 465399986, 455177047, 445192821, 435441069, 425915746, 416610992, 407521128, 398640646, 389964206, 381486626, 373202880, 365108089, 357197520, 349466575, 341910791, 334525835, 327307496, 320251684, 313354423, 306611852, 300020216, 293575864, 287275246, 281114911, 275091501, 269201750, 263442479, 257810595, 252303089, 246917031]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 754).prefactor = (2418275023126507/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 754).cutoff/(generalMeanRows 754).c)).2 =
    (14573220115251/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 754).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 754).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 754).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 754

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 754).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 754).criticalRate j.val*(generalMeanRows 754).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 754).c*(generalMeanRows 754).criticalPoint j.val)).2-
      (generalMeanRows 754).J/2-(generalMeanRows 754).error (generalMeanGrid j.val)+
      (generalMeanRows 754).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 754).c)).2-
      (generalMeanRows 754).J/2-(generalMeanRows 754).error 4 := by
  have he : (generalMeanRows 754).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 754) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 754)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0754

/-! Kernel-checked entropy margins for general spectral rectangle 755. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0755
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5305865244, 5128363158, 4958706325, 4796449952, 4641180604, 4492513464, 4350089888, 4213575224, 4082656850, 3957042405, 3836458202, 3720647788, 3609370632, 3502400947, 3399526606, 3300548161, 3205277936, 3113539212, 3025165467, 2939999681, 2857893704, 2778707662, 2702309418, 2628574073, 2557383501, 2488625920, 2422195498, 2357991985, 2295920365, 2235890548, 2177817064, 2121618796, 2067218719, 2014543662, 1963524083, 1914093864, 1866190112, 1819752979, 1774725489, 1731053381, 1688684958, 1647570943, 1607664354, 1568920373, 1531296235, 1494751116, 1459246030, 1424743734, 1391208638, 1358606716, 1326905428, 1296073641, 1266081563, 1236900670, 1208503644, 1180864314, 1153957598, 1127759450, 1102246810, 1077397552, 1053190447, 1029605112, 1006621972, 984222226, 962387804, 941101337, 920346124, 900106099, 880365805, 861110365, 842325453, 823997274, 806112537, 788658434, 771622617, 754993180, 738758639, 722907913, 707430309, 692315501, 677553520, 663134734, 649049838, 635289837, 621846036, 608710027, 595873674, 583329109, 571068714, 559085115, 547371173, 535919973, 524724814, 513779204, 503076850, 492611652, 482377693, 472369234, 462580708, 453006712, 443642002, 434481487, 425520223, 416753409, 408176381, 399784607, 391573682, 383539325, 375677373, 367983781, 360454610, 353086032, 345874322, 338815854, 331907101, 325144627, 318525088, 312045229, 305701878, 299491946, 293412425]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 755).prefactor = (4870502885269041/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 755).cutoff/(generalMeanRows 755).c)).2 =
    (94772729616099/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 755).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 755).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 755).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 755

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 755).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 755).criticalRate j.val*(generalMeanRows 755).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 755).c*(generalMeanRows 755).criticalPoint j.val)).2-
      (generalMeanRows 755).J/2-(generalMeanRows 755).error (generalMeanGrid j.val)+
      (generalMeanRows 755).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 755).c)).2-
      (generalMeanRows 755).J/2-(generalMeanRows 755).error 4 := by
  have he : (generalMeanRows 755).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 755) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 755)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0755

/-! Kernel-checked entropy margins for general spectral rectangle 756. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0756
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5336405834, 5153092512, 4977936185, 4810475856, 4650282912, 4496958303, 4350130019, 4209450834, 4074596285, 3945262847, 3821166295, 3702040218, 3587634667, 3477714940, 3372060463, 3270463776, 3172729604, 3078674012, 2988123618, 2900914887, 2816893464, 2735913573, 2657837459, 2582534868, 2509882570, 2439763920, 2372068445, 2306691467, 2243533746, 2182501156, 2123504375, 2066458606, 2011283306, 1957901944, 1906241765, 1856233580, 1807811557, 1760913038, 1715478361, 1671450693, 1628775875, 1587402276, 1547280660, 1508364051, 1470607618, 1433968561, 1398406000, 1363880880, 1330355873, 1297795292, 1266165003, 1235432352, 1205566083, 1176536275, 1148314270, 1120872615, 1094184998, 1068226198, 1042972025, 1018399278, 994485691, 971209892, 948551360, 926490384, 905008026, 884086086, 863707066, 843854138, 824511116, 805662423, 787293067, 769388614, 751935159, 734919311, 718328163, 702149273, 686370647, 670980715, 655968315, 641322678, 627033405, 613090460, 599484147, 586205102, 573244274, 560592917, 548242575, 536185071, 524412494, 512917193, 501691762, 490729032, 480022063, 469564133, 459348734, 449369555, 439620485, 430095599, 420789153, 411695575, 402809464, 394125578, 385638831, 377344287, 369237155, 361312784, 353566656, 345994384, 338591706, 331354481, 324278684, 317360404, 310595840, 303981293, 297513169, 291187971, 285002297, 278952838, 273036375, 267249772, 261589980]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 756).prefactor = (501967257060917/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 756).cutoff/(generalMeanRows 756).c)).2 =
    (361735217957953/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 756).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 756).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 756).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 756

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 756).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 756).criticalRate j.val*(generalMeanRows 756).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 756).c*(generalMeanRows 756).criticalPoint j.val)).2-
      (generalMeanRows 756).J/2-(generalMeanRows 756).error (generalMeanGrid j.val)+
      (generalMeanRows 756).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 756).c)).2-
      (generalMeanRows 756).J/2-(generalMeanRows 756).error 4 := by
  have he : (generalMeanRows 756).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 756) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 756)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0756

/-! Kernel-checked entropy margins for general spectral rectangle 757. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0757
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5101708684, 4932085954, 4770003614, 4615029284, 4466761300, 4324826029, 4188875475, 4058585137, 3933652084, 3813793218, 3698743715, 3588255609, 3482096507, 3380048425, 3281906726, 3187479154, 3096584944, 3009054019, 2924726241, 2843450733, 2765085251, 2689495606, 2616555131, 2546144192, 2478149730, 2412464844, 2348988398, 2287624661, 2228282976, 2170877441, 2115326625, 2061553295, 2009484169, 1959049677, 1910183747, 1862823598, 1816909552, 1772384853, 1729195506, 1687290115, 1646619741, 1607137763, 1568799752, 1531563350, 1495388156, 1460235622, 1426068952, 1392853010, 1360554230, 1329140535, 1298581258, 1268847071, 1239909913, 1211742927, 1184320398, 1157617696, 1131611219, 1106278345, 1081597383, 1057547524, 1034108802, 1011262049, 988988860, 967271555, 946093143, 925437292, 905288297, 885631049, 866451010, 847734185, 829467100, 811636773, 794230696, 777236813, 760643500, 744439545, 728614131, 713156816, 698057523, 683306517, 668894396, 654812072, 641050765, 627601982, 614457510, 601609404, 589049976, 576771783, 564767618, 553030502, 541553675, 530330583, 519354877, 508620400, 498121180, 487851427, 477805520, 467978007, 458363594, 448957141, 439753657, 430748293, 421936340, 413313219, 404874482, 396615803, 388532976, 380621910, 372878626, 365299253, 357880024, 350617272, 343507426, 336547013, 329732647, 323061033, 316528959, 310133297, 303870998, 297739093, 291734684]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 757).prefactor = (592541284316151/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 757).cutoff/(generalMeanRows 757).c)).2 =
    (397164546898687/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 757).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 757).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 757).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 757

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 757).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 757).criticalRate j.val*(generalMeanRows 757).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 757).c*(generalMeanRows 757).criticalPoint j.val)).2-
      (generalMeanRows 757).J/2-(generalMeanRows 757).error (generalMeanGrid j.val)+
      (generalMeanRows 757).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 757).c)).2-
      (generalMeanRows 757).J/2-(generalMeanRows 757).error 4 := by
  have he : (generalMeanRows 757).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 757) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 757)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0757

/-! Kernel-checked entropy margins for general spectral rectangle 758. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0758
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5432265093, 5253082616, 5081790450, 4917940885, 4761117804, 4610933921, 4467028321, 4329064259, 4196727183, 4069722951, 3947776233, 3830629057, 3718039492, 3609780454, 3505638618, 3405413426, 3308916181, 3215969214, 3126405125, 3040066084, 2956803189, 2876475871, 2798951349, 2724104128, 2651815530, 2581973265, 2514471026, 2449208126, 2386089146, 2325023618, 2265925728, 2208714036, 2153311221, 2099643835, 2047642083, 1997239610, 1948373305, 1900983118, 1855011886, 1810405174, 1767111123, 1725080309, 1684265609, 1644622080, 1606106835, 1568678940, 1532299306, 1496930596, 1462537127, 1429084791, 1396540970, 1364874459, 1334055396, 1304055192, 1274846470, 1246403000, 1218699647, 1191712313, 1165417888, 1139794201, 1114819977, 1090474789, 1066739023, 1043593836, 1021021119, 999003467, 977524139, 956567036, 936116663, 916158109, 896677013, 877659546, 859092382, 840962680, 823258058, 805966576, 789076717, 772577366, 756457795, 740707645, 725316912, 710275930, 695575358, 681206168, 667159627, 653427293, 640000995, 626872826, 614035133, 601480506, 589201766, 577191962, 565444354, 553952413, 542709807, 531710395, 520948221, 510417508, 500112647, 490028196, 480158869, 470499534, 461045207, 451791044, 442732339, 433864519, 425183135, 416683864, 408362502, 400214957, 392237250, 384425509, 376775965, 369284948, 361948886, 354764301, 347727805, 340836097, 334085962, 327474267, 320997958]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 758).prefactor = (2452347037511983/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 758).cutoff/(generalMeanRows 758).c)).2 =
    (77310727933197/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 758).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 758).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 758).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 758

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 758).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 758).criticalRate j.val*(generalMeanRows 758).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 758).c*(generalMeanRows 758).criticalPoint j.val)).2-
      (generalMeanRows 758).J/2-(generalMeanRows 758).error (generalMeanGrid j.val)+
      (generalMeanRows 758).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 758).c)).2-
      (generalMeanRows 758).J/2-(generalMeanRows 758).error 4 := by
  have he : (generalMeanRows 758).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 758) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 758)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0758

/-! Kernel-checked entropy margins for general spectral rectangle 759. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0759
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5655899056, 5474693893, 5301412828, 5135605335, 4976852742, 4824765442, 4678980418, 4539159014, 4404984945, 4276162502, 4152414935, 4033482987, 3919123566, 3809108542, 3703223650, 3601267484, 3503050587, 3408394613, 3317131557, 3229103052, 3144159718, 3062160570, 2982972459, 2906469571, 2832532952, 2761050076, 2691914438, 2625025182, 2560286754, 2497608577, 2436904755, 2378093785, 2321098306, 2265844850, 2212263616, 2160288258, 2109855690, 2060905897, 2013381762, 1967228906, 1922395535, 1878832295, 1836492141, 1795330212, 1755303711, 1716371793, 1678495465, 1641637484, 1605762270, 1570835813, 1536825595, 1503700512, 1471430804, 1439987984, 1409344772, 1379475039, 1350353746, 1321956891, 1294261458, 1267245369, 1240887436, 1215167321, 1190065493, 1165563191, 1141642386, 1118285748, 1095476609, 1073198940, 1051437312, 1030176879, 1009403339, 989102920, 969262352, 949868841, 930910056, 912374099, 894249493, 876525162, 859190412, 842234914, 825648694, 809422109, 793545841, 778010879, 762808508, 747930297, 733368085, 719113973, 705160311, 691499691, 678124934, 665029082, 652205393, 639647325, 627348536, 615302872, 603504361, 591947206, 580625779, 569534614, 558668402, 548021983, 537590344, 527368611, 517352046, 507536039, 497916108, 488487892, 479247146, 470189739, 461311649, 452608960, 444077857, 435714625, 427515645, 419477388, 411596416, 403869377, 396293005, 388864112, 381579590]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 759).prefactor = (4939125288752673/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 759).cutoff/(generalMeanRows 759).c)).2 =
    (401648265888471/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 759).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 759).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 759).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 759

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 759).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 759).criticalRate j.val*(generalMeanRows 759).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 759).c*(generalMeanRows 759).criticalPoint j.val)).2-
      (generalMeanRows 759).J/2-(generalMeanRows 759).error (generalMeanGrid j.val)+
      (generalMeanRows 759).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 759).c)).2-
      (generalMeanRows 759).J/2-(generalMeanRows 759).error 4 := by
  have he : (generalMeanRows 759).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 759) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 759)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0759

/-! Kernel-checked entropy margins for general spectral rectangle 760. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0760
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5324389597, 5152451078, 4988048796, 4830753603, 4680166737, 4535917162, 4397659201, 4265070416, 4137849708, 4015715598, 3898404690, 3785670268, 3677281028, 3573019933, 3472683161, 3376079147, 3283027715, 3193359275, 3106914092, 3023541609, 2943099833, 2865454762, 2790479859, 2718055567, 2648068862, 2580412833, 2514986304, 2451693469, 2390443569, 2331150575, 2273732911, 2218113180, 2164217917, 2111977362, 2061325238, 2012198550, 1964537401, 1918284810, 1873386549, 1829790991, 1787448960, 1746313601, 1706340246, 1667486302, 1629711134, 1592975961, 1557243755, 1522479154, 1488648367, 1455719095, 1423660455, 1392442905, 1362038174, 1332419200, 1303560067, 1275435948, 1248023051, 1221298565, 1195240615, 1169828215, 1145041222, 1120860301, 1097266879, 1074243115, 1051771860, 1029836628, 1008421565, 987511416, 967091500, 947147684, 927666358, 908634408, 890039198, 871868545, 854110704, 836754341, 819788522, 803202692, 786986661, 771130584, 755624951, 740460572, 725628559, 711120322, 696927547, 683042191, 669456471, 656162849, 643154027, 630422934, 617962718, 605766740, 593828561, 582141939, 570700817, 559499320, 548531745, 537792557, 527276381, 516977997, 506892333, 497014463, 487339597, 477863081, 468580387, 459487115, 450578981, 441851821, 433301580, 424924311, 416716174, 408673427, 400792429, 393069630, 385501573, 378084891, 370816299, 363692599, 356710670, 349867471, 343160033]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 760).prefactor = (2363392450278567/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 760).cutoff/(generalMeanRows 760).c)).2 =
    (400743559416903/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 760).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 760).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 760).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 760

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 760).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 760).criticalRate j.val*(generalMeanRows 760).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 760).c*(generalMeanRows 760).criticalPoint j.val)).2-
      (generalMeanRows 760).J/2-(generalMeanRows 760).error (generalMeanGrid j.val)+
      (generalMeanRows 760).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 760).c)).2-
      (generalMeanRows 760).J/2-(generalMeanRows 760).error 4 := by
  have he : (generalMeanRows 760).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 760) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 760)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0760

/-! Kernel-checked entropy margins for general spectral rectangle 761. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0761
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5451304117, 5277847222, 5111967361, 4953232588, 4801241565, 4655620890, 4516022713, 4382122593, 4253617585, 4130224514, 4011678417, 3897731133, 3788150030, 3682716841, 3581226612, 3483486733, 3389316065, 3298544128, 3211010365, 3126563466, 3045060738, 2966367536, 2890356730, 2816908217, 2745908470, 2677250115, 2610831548, 2546556573, 2484334067, 2424077675, 2365705512, 2309139903, 2254307128, 2201137191, 2149563601, 2099523167, 2050955811, 2003804389, 1958014524, 1913534450, 1870314868, 1828308810, 1787471507, 1747760271, 1709134384, 1671554986, 1634984983, 1599388948, 1564733035, 1530984895, 1498113598, 1466089560, 1434884475, 1404471247, 1374823931, 1345917671, 1317728652, 1290234042, 1263411946, 1237241360, 1211702125, 1186774891, 1162441072, 1138682814, 1115482958, 1092825006, 1070693093, 1049071955, 1027946903, 1007303792, 987129004, 967409415, 948132381, 929285709, 910857643, 892836841, 875212358, 857973628, 841110449, 824612967, 808471657, 792677318, 777221049, 762094244, 747288577, 732795989, 718608681, 704719100, 691119929, 677804081, 664764685, 651995084, 639488819, 627239627, 615241431, 603488334, 591974612, 580694706, 569643218, 558814903, 548204668, 537807558, 527618759, 517633591, 507847499, 498256055, 488854949, 479639986, 470607084, 461752267, 453071664, 444561505, 436218116, 428037918, 420017422, 412153229, 404442023, 396880572, 389465724, 382194403, 375063609]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 761).prefactor = (4759322692815191/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 761).cutoff/(generalMeanRows 761).c)).2 =
    (408234231146061/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 761).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 761).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 761).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 761

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 761).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 761).criticalRate j.val*(generalMeanRows 761).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 761).c*(generalMeanRows 761).criticalPoint j.val)).2-
      (generalMeanRows 761).J/2-(generalMeanRows 761).error (generalMeanGrid j.val)+
      (generalMeanRows 761).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 761).c)).2-
      (generalMeanRows 761).J/2-(generalMeanRows 761).error 4 := by
  have he : (generalMeanRows 761).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 761) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 761)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0761

/-! Kernel-checked entropy margins for general spectral rectangle 762. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0762
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5061295524, 4888503491, 4723372681, 4565470090, 4414393173, 4269767185, 4131242808, 3998494034, 3871216254, 3749124550, 3631952145, 3519449008, 3411380587, 3307526655, 3207680261, 3111646781, 3019243037, 2930296500, 2844644558, 2762133843, 2682619610, 2605965167, 2532041349, 2460726033, 2391903690, 2325464964, 2261306295, 2199329554, 2139441714, 2081554542, 2025584311, 1971451535, 1919080715, 1868400110, 1819341522, 1771840087, 1725834093, 1681264795, 1638076257, 1596215189, 1555630809, 1516274699, 1478100681, 1441064696, 1405124692, 1370240514, 1336373807, 1303487923, 1271547829, 1240520027, 1210372473, 1181074505, 1152596773, 1124911169, 1097990774, 1071809789, 1046343488, 1021568160, 997461063, 974000377, 951165157, 928935296, 907291479, 886215153, 865688487, 845694338, 826216222, 807238282, 788745260, 770722470, 753155773, 736031549, 719336680, 703058523, 687184891, 671704032, 656604613, 641875701, 627506741, 613487550, 599808290, 586459464, 573431893, 560716710, 548305343, 536189504, 524361178, 512812612, 501536305, 490524995, 479771655, 469269480, 459011878, 448992465, 439205054, 429643650, 420302440, 411175789, 402258232, 393544468, 385029352, 376707895, 368575251, 360626718, 352857730, 345263851, 337840775, 330584315, 323490406, 316555095, 309774541, 303145009, 296662867, 290324582, 284126721, 278065939, 272138987, 266342698, 260673993, 255129873, 249707420]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 762).prefactor = (2384528116498167/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 762).cutoff/(generalMeanRows 762).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 762).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 762).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 762).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 762

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 762).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 762).criticalRate j.val*(generalMeanRows 762).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 762).c*(generalMeanRows 762).criticalPoint j.val)).2-
      (generalMeanRows 762).J/2-(generalMeanRows 762).error (generalMeanGrid j.val)+
      (generalMeanRows 762).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 762).c)).2-
      (generalMeanRows 762).J/2-(generalMeanRows 762).error 4 := by
  have he : (generalMeanRows 762).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 762) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 762)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0762

/-! Kernel-checked entropy margins for general spectral rectangle 763. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0763
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5266005898, 5091079806, 4923849574, 4763879671, 4610765262, 4464129528, 4323621271, 4188912778, 4059697898, 3935690318, 3816621998, 3702241766, 3592314039, 3486617661, 3384944846, 3287100216, 3192899919, 3102170823, 3014749776, 2930482928, 2849225108, 2770839245, 2695195842, 2622172483, 2551653384, 2483528969, 2417695486, 2354054644, 2292513279, 2232983044, 2175380119, 2119624941, 2065641955, 2013359378, 1962708980, 1913625882, 1866048363, 1819917683, 1775177914, 1731775788, 1689660544, 1648783795, 1609099398, 1570563331, 1533133582, 1496770040, 1461434397, 1427090050, 1393702014, 1361236838, 1329662528, 1298948467, 1269065353, 1239985125, 1211680907, 1184126945, 1157298553, 1131172060, 1105724762, 1080934874, 1056781485, 1033244517, 1010304686, 987943462, 966143038, 944886291, 924156755, 903938588, 884216543, 864975943, 846202655, 827883064, 810004051, 792552971, 775517632, 758886275, 742647557, 726790529, 711304623, 696179636, 681405711, 666973325, 652873275, 639096664, 625634891, 612479634, 599622843, 587056727, 574773746, 562766597, 551028208, 539551730, 528330522, 517358153, 506628383, 496135165, 485872632, 475835092, 466017024, 456413067, 447018017, 437826823, 428834575, 420036509, 411427991, 403004522, 394761726, 386695349, 378801256, 371075424, 363513941, 356113000, 348868896, 341778024, 334836876, 328042033, 321390169, 314878044, 308502501, 302260467, 296148944]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 763).prefactor = (2401220136712229/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 763).cutoff/(generalMeanRows 763).c)).2 =
    (190178714291153/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 763).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 763).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 763).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 763

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 763).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 763).criticalRate j.val*(generalMeanRows 763).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 763).c*(generalMeanRows 763).criticalPoint j.val)).2-
      (generalMeanRows 763).J/2-(generalMeanRows 763).error (generalMeanGrid j.val)+
      (generalMeanRows 763).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 763).c)).2-
      (generalMeanRows 763).J/2-(generalMeanRows 763).error 4 := by
  have he : (generalMeanRows 763).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 763) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 763)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0763

/-! Kernel-checked entropy margins for general spectral rectangle 764. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0764
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5253244344, 5076313342, 4907196213, 4745451063, 4590667113, 4442461980, 4300479258, 4164386342, 4033872490, 3908647069, 3788437972, 3672990196, 3562064541, 3455436439, 3352894878, 3254241427, 3159289347, 3067862768, 2979795945, 2894932566, 2813125124, 2734234330, 2658128577, 2584683443, 2513781236, 2445310564, 2379165944, 2315247436, 2253460306, 2193714706, 2135925388, 2080011425, 2025895956, 1973505955, 1922772003, 1873628084, 1826011392, 1779862146, 1735123426, 1691741012, 1649663234, 1608840834, 1569226833, 1530776414, 1493446797, 1457197141, 1421988434, 1387783400, 1354546411, 1322243398, 1290841772, 1260310351, 1230619287, 1201739998, 1173645105, 1146308375, 1119704662, 1093809852, 1068600819, 1044055370, 1020152204, 996870870, 974191725, 952095895, 930565242, 909582328, 889130383, 869193273, 849755473, 830802039, 812318579, 794291234, 776706649, 759551952, 742814736, 726483034, 710545304, 694990407, 679807593, 664986483, 650517055, 636389626, 622594840, 609123654, 595967326, 583117403, 570565705, 558304321, 546325593, 534622108, 523186690, 512012385, 501092460, 490420390, 479989849, 469794706, 459829016, 450087013, 440563104, 431251860, 422148014, 413246454, 404542215, 396030475, 387706553, 379565898, 371604092, 363816837, 356199959, 348749397, 341461203, 334331538, 327356667, 320532956, 313856871, 307324969, 300933901, 294680407, 288561312, 282573525, 276714032]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 764).prefactor = (4869911068594073/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 764).cutoff/(generalMeanRows 764).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 764).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 764).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 764).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 764

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 764).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 764).criticalRate j.val*(generalMeanRows 764).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 764).c*(generalMeanRows 764).criticalPoint j.val)).2-
      (generalMeanRows 764).J/2-(generalMeanRows 764).error (generalMeanGrid j.val)+
      (generalMeanRows 764).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 764).c)).2-
      (generalMeanRows 764).J/2-(generalMeanRows 764).error 4 := by
  have he : (generalMeanRows 764).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 764) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 764)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0764

/-! Kernel-checked entropy margins for general spectral rectangle 765. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0765
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5783832037, 5596025561, 5416453586, 5244649299, 5080178805, 4922638252, 4771651268, 4626866659, 4487956360, 4354613575, 4226551110, 4103499857, 3985207429, 3871436913, 3761965736, 3656584633, 3555096703, 3457316546, 3363069466, 3272190746, 3184524981, 3099925457, 3018253582, 2939378366, 2863175931, 2789529063, 2718326792, 2649464012, 2582841117, 2518363667, 2455942081, 2395491346, 2336930747, 2280183615, 2225177095, 2171841924, 2120112229, 2069925332, 2021221572, 1973944138, 1928038911, 1883454313, 1840141174, 1798052598, 1757143839, 1717372193, 1678696884, 1641078962, 1604481213, 1568868063, 1534205497, 1500460977, 1467603367, 1435602864, 1404430927, 1374060219, 1344464542, 1315618784, 1287498864, 1260081684, 1233345080, 1207267773, 1181829336, 1157010143, 1132791339, 1109154800, 1086083099, 1063559474, 1041567799, 1020092552, 999118789, 978632119, 958618678, 939065102, 919958511, 901286486, 883037044, 865198625, 847760070, 830710607, 814039830, 797737688, 781794467, 766200778, 750947542, 736025978, 721427590, 707144156, 693167718, 679490569, 666105246, 653004516, 640181373, 627629024, 615340883, 603310562, 591531867, 579998783, 568705477, 557646284, 546815704, 536208394, 525819165, 515642974, 505674919, 495910237, 486344294, 476972586, 467790730, 458794462, 449979633, 441342204, 432878243, 424583922, 416455513, 408489384, 400681998, 393029907, 385529752, 378178257, 370972230]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 765).prefactor = (1018352884035543/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 765).cutoff/(generalMeanRows 765).c)).2 =
    (391926190237101/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 765).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 765).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 765).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 765

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 765).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 765).criticalRate j.val*(generalMeanRows 765).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 765).c*(generalMeanRows 765).criticalPoint j.val)).2-
      (generalMeanRows 765).J/2-(generalMeanRows 765).error (generalMeanGrid j.val)+
      (generalMeanRows 765).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 765).c)).2-
      (generalMeanRows 765).J/2-(generalMeanRows 765).error 4 := by
  have he : (generalMeanRows 765).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 765) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 765)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0765

/-! Kernel-checked entropy margins for general spectral rectangle 766. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0766
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5001385059, 4830397386, 4667070053, 4510964438, 4361673016, 4218816647, 4082042147, 3951020124, 3825443028, 3705023401, 3589492288, 3478597814, 3372103877, 3269788978, 3171445137, 3076876923, 2985900552, 2898343069, 2814041600, 2732842656, 2654601503, 2579181578, 2506453946, 2436296807, 2368595030, 2303239736, 2240127897, 2179161971, 2120249567, 2063303124, 2008239622, 1954980308, 1903450438, 1853579048, 1805298724, 1758545401, 1713258170, 1669379095, 1626853045, 1585627540, 1545652596, 1506880594, 1469266145, 1432765970, 1397338783, 1362945190, 1329547581, 1297110038, 1265598248, 1234979413, 1205222180, 1176296556, 1148173847, 1120826587, 1094228478, 1068354329, 1043180004, 1018682366, 994839230, 971629315, 949032203, 927028294, 905598766, 884725543, 864391255, 844579205, 825273340, 806458221, 788118991, 770241353, 752811541, 735816299, 719242854, 703078901, 687312576, 671932437, 656927451, 642286972, 628000725, 614058789, 600451586, 587169862, 574204676, 561547387, 549189640, 537123356, 525340721, 513834173, 502596395, 491620303, 480899037, 470425954, 460194619, 450198794, 440432435, 430889683, 421564853, 412452436, 403547085, 394843611, 386336979, 378022302, 369894834, 361949967, 354183223, 346590253, 339166832, 331908853, 324812322, 317873359, 311088189, 304453141, 297964644, 291619225, 285413503, 279344187, 273408077, 267602054, 261923084, 256368211, 250934556]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 766).prefactor = (1200922140434843/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 766).cutoff/(generalMeanRows 766).c)).2 =
    (76513149495507/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 766).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 766).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 766).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 766

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 766).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 766).criticalRate j.val*(generalMeanRows 766).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 766).c*(generalMeanRows 766).criticalPoint j.val)).2-
      (generalMeanRows 766).J/2-(generalMeanRows 766).error (generalMeanGrid j.val)+
      (generalMeanRows 766).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 766).c)).2-
      (generalMeanRows 766).J/2-(generalMeanRows 766).error 4 := by
  have he : (generalMeanRows 766).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 766) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 766)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0766

/-! Kernel-checked entropy margins for general spectral rectangle 767. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0767
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5594761995, 5405320600, 5224244591, 5051062994, 4885337874, 4726661447, 4574653511, 4428959146, 4289246648, 4155205669, 4026545551, 3902993802, 3784294729, 3670208191, 3560508461, 3454983195, 3353432482, 3255667985, 3161512139, 3070797427, 2983365710, 2899067608, 2817761928, 2739315143, 2663600900, 2590499574, 2519897848, 2451688327, 2385769175, 2322043785, 2260420464, 2200812145, 2143136115, 2087313764, 2033270349, 1980934774, 1930239382, 1881119766, 1833514587, 1787365403, 1742616513, 1699214808, 1657109628, 1616252638, 1576597698, 1538100748, 1500719703, 1464414348, 1429146239, 1394878618, 1361576320, 1329205699, 1297734547, 1267132023, 1237368587, 1208415935, 1180246936, 1152835580, 1126156917, 1100187013, 1074902895, 1050282511, 1026304682, 1002949064, 980196107, 958027021, 936423737, 915368878, 894845724, 874838186, 855330773, 836308570, 817757211, 799662851, 782012150, 764792246, 747990734, 731595651, 715595452, 699978995, 684735524, 669854653, 655326347, 641140914, 627288984, 613761503, 600549712, 587645142, 575039601, 562725159, 550694143, 538939123, 527452905, 516228520, 505259217, 494538454, 484059890, 473817378, 463804955, 454016841, 444447425, 435091266, 425943082, 416997745, 408250276, 399695842, 391329745, 383147426, 375144450, 367316511, 359659420, 352169108, 344841615, 337673092, 330659795, 323798079, 317084402, 310515312, 304087452, 297797554, 291642435]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 767).prefactor = (642784292491533/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 767).cutoff/(generalMeanRows 767).c)).2 =
    (45445515180161/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 767).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 767).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 767).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 767

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 767).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 767).criticalRate j.val*(generalMeanRows 767).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 767).c*(generalMeanRows 767).criticalPoint j.val)).2-
      (generalMeanRows 767).J/2-(generalMeanRows 767).error (generalMeanGrid j.val)+
      (generalMeanRows 767).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 767).c)).2-
      (generalMeanRows 767).J/2-(generalMeanRows 767).error 4 := by
  have he : (generalMeanRows 767).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 767) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 767)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0767

/-! Kernel-checked entropy margins for general spectral rectangle 768. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0768
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4915377277, 4742855708, 4578100377, 4420668944, 4270150284, 4126161767, 3988346826, 3856372784, 3729928898, 3608724607, 3492487942, 3380964092, 3273914105, 3171113705, 3072352217, 2977431583, 2886165466, 2798378432, 2713905193, 2632589917, 2554285591, 2478853439, 2406162378, 2336088518, 2268514706, 2203330096, 2140429753, 2079714287, 2021089515, 1964466138, 1909759454, 1856889078, 1805778691, 1756355798, 1708551510, 1662300331, 1617539969, 1574211153, 1532257461, 1491625164, 1452263076, 1414122412, 1377156663, 1341321466, 1306574493, 1272875341, 1240185432, 1208467912, 1177687568, 1147810736, 1118805228, 1090640251, 1063286337, 1036715279, 1010900066, 985814823, 961434756, 937736095, 914696052, 892292765, 870505258, 849313398, 828697852, 808640055, 789122169, 770127049, 751638215, 733639818, 716116612, 699053926, 682437640, 666254158, 650490388, 635133713, 620171980, 605593470, 591386886, 577541332, 564046294, 550891630, 538067548, 525564593, 513373635, 501485855, 489892728, 478586020, 467557765, 456800265, 446306070, 436067976, 426079011, 416332424, 406821683, 397540460, 388482628, 379642251, 371013576, 362591027, 354369201, 346342858, 338506917, 330856447, 323386668, 316092940, 308970760, 302015756, 295223685, 288590426, 282111977, 275784450, 269604068, 263567162, 257670164, 251909608, 246282124, 240784435, 235413354, 230165782, 225038706, 220029191, 215134385]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 768).prefactor = (2423441689413217/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 768).cutoff/(generalMeanRows 768).c)).2 =
    (181271596153589/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 768).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 768).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 768).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 768

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 768).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 768).criticalRate j.val*(generalMeanRows 768).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 768).c*(generalMeanRows 768).criticalPoint j.val)).2-
      (generalMeanRows 768).J/2-(generalMeanRows 768).error (generalMeanGrid j.val)+
      (generalMeanRows 768).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 768).c)).2-
      (generalMeanRows 768).J/2-(generalMeanRows 768).error 4 := by
  have he : (generalMeanRows 768).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 768) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 768)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0768

/-! Kernel-checked entropy margins for general spectral rectangle 769. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0769
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5034697862, 4862571289, 4698156078, 4541010688, 4390724879, 4246916984, 4109231468, 3977336744, 3850923216, 3729701507, 3613400875, 3501767764, 3394564502, 3291568112, 3192569231, 3097371125, 3005788786, 2917648108, 2832785130, 2751045343, 2672283048, 2596360773, 2523148723, 2452524286, 2384371567, 2318580961, 2255048751, 2193676749, 2134371946, 2077046199, 2021615935, 1968001875, 1916128780, 1865925211, 1817323305, 1770258572, 1724669695, 1680498354, 1637689050, 1596188954, 1555947748, 1516917497, 1479052509, 1442309216, 1406646059, 1372023380, 1338403319, 1305749719, 1274028038, 1243205260, 1213249821, 1184131532, 1155821506, 1128292094, 1101516822, 1075470334, 1050128329, 1025467519, 1001465571, 978101062, 955353437, 933202965, 911630702, 890618448, 870148719, 850204706, 830770251, 811829809, 793368427, 775371711, 757825804, 740717361, 724033526, 707761910, 691890569, 676407988, 661303058, 646565063, 632183659, 618148860, 604451023, 591080833, 578029290, 565287694, 552847635, 540700982, 528839866, 517256676, 505944046, 494894845, 484102169, 473559328, 463259844, 453197440, 443366031, 433759716, 424372777, 415199664, 406234997, 397473552, 388910260, 380540201, 372358599, 364360812, 356542336, 348898792, 341425926, 334119603, 326975804, 319990623, 313160259, 306481017, 299949302, 293561618, 287314561, 281204820, 275229170, 269384475, 263667679, 258075806, 252605959]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 769).prefactor = (2417842282090307/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 769).cutoff/(generalMeanRows 769).c)).2 =
    (76513149495507/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 769).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 769).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 769).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 769

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 769).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 769).criticalRate j.val*(generalMeanRows 769).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 769).c*(generalMeanRows 769).criticalPoint j.val)).2-
      (generalMeanRows 769).J/2-(generalMeanRows 769).error (generalMeanGrid j.val)+
      (generalMeanRows 769).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 769).c)).2-
      (generalMeanRows 769).J/2-(generalMeanRows 769).error 4 := by
  have he : (generalMeanRows 769).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 769) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 769)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0769

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock10 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 10 i) := by
  fin_cases i
  · exact EntropyRow0700.numerical
  · exact EntropyRow0701.numerical
  · exact EntropyRow0702.numerical
  · exact EntropyRow0703.numerical
  · exact EntropyRow0704.numerical
  · exact EntropyRow0705.numerical
  · exact EntropyRow0706.numerical
  · exact EntropyRow0707.numerical
  · exact EntropyRow0708.numerical
  · exact EntropyRow0709.numerical
  · exact EntropyRow0710.numerical
  · exact EntropyRow0711.numerical
  · exact EntropyRow0712.numerical
  · exact EntropyRow0713.numerical
  · exact EntropyRow0714.numerical
  · exact EntropyRow0715.numerical
  · exact EntropyRow0716.numerical
  · exact EntropyRow0717.numerical
  · exact EntropyRow0718.numerical
  · exact EntropyRow0719.numerical
  · exact EntropyRow0720.numerical
  · exact EntropyRow0721.numerical
  · exact EntropyRow0722.numerical
  · exact EntropyRow0723.numerical
  · exact EntropyRow0724.numerical
  · exact EntropyRow0725.numerical
  · exact EntropyRow0726.numerical
  · exact EntropyRow0727.numerical
  · exact EntropyRow0728.numerical
  · exact EntropyRow0729.numerical
  · exact EntropyRow0730.numerical
  · exact EntropyRow0731.numerical
  · exact EntropyRow0732.numerical
  · exact EntropyRow0733.numerical
  · exact EntropyRow0734.numerical
  · exact EntropyRow0735.numerical
  · exact EntropyRow0736.numerical
  · exact EntropyRow0737.numerical
  · exact EntropyRow0738.numerical
  · exact EntropyRow0739.numerical
  · exact EntropyRow0740.numerical
  · exact EntropyRow0741.numerical
  · exact EntropyRow0742.numerical
  · exact EntropyRow0743.numerical
  · exact EntropyRow0744.numerical
  · exact EntropyRow0745.numerical
  · exact EntropyRow0746.numerical
  · exact EntropyRow0747.numerical
  · exact EntropyRow0748.numerical
  · exact EntropyRow0749.numerical
  · exact EntropyRow0750.numerical
  · exact EntropyRow0751.numerical
  · exact EntropyRow0752.numerical
  · exact EntropyRow0753.numerical
  · exact EntropyRow0754.numerical
  · exact EntropyRow0755.numerical
  · exact EntropyRow0756.numerical
  · exact EntropyRow0757.numerical
  · exact EntropyRow0758.numerical
  · exact EntropyRow0759.numerical
  · exact EntropyRow0760.numerical
  · exact EntropyRow0761.numerical
  · exact EntropyRow0762.numerical
  · exact EntropyRow0763.numerical
  · exact EntropyRow0764.numerical
  · exact EntropyRow0765.numerical
  · exact EntropyRow0766.numerical
  · exact EntropyRow0767.numerical
  · exact EntropyRow0768.numerical
  · exact EntropyRow0769.numerical
end SingularValueBounds.KL.Certificates
