import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 770. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0770
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4985549663, 4812780490, 4647782947, 4490112281, 4339355240, 4195127325, 4057070335, 3924850171, 3798154863, 3676692797, 3560191111, 3448394244, 3341062622, 3237971469, 3138909708, 3043678982, 2952092738, 2863975400, 2779161610, 2697495526, 2618830181, 2543026891, 2469954709, 2399489922, 2331515582, 2265921079, 2202601739, 2141458456, 2082397346, 2025329425, 1970170321, 1916839987, 1865262449, 1815365566, 1767080804, 1720343027, 1675090304, 1631263722, 1588807218, 1547667421, 1507793495, 1469137007, 1431651790, 1395293819, 1360021100, 1325793556, 1292572925, 1260322667, 1229007873, 1198595176, 1169052673, 1140349854, 1112457522, 1085347734, 1058993732, 1033369890, 1008451649, 984215473, 960638791, 937699957, 915378199, 893653580, 872506958, 851919946, 831874880, 812354782, 793343329, 774824822, 756784159, 739206808, 722078776, 705386591, 689117277, 673258330, 657797698, 642723762, 628025317, 613691553, 599712040, 586076709, 572775841, 559800046, 547140255, 534787706, 522733928, 510970731, 499490197, 488284663, 477346718, 466669189, 456245131, 446067821, 436130746, 426427598, 416952264, 407698821, 398661526, 389834811, 381213276, 372791682, 364564948, 356528141, 348676477, 341005307, 333510119, 326186532, 319030289, 312037255, 305203412, 298524855, 291997788, 285618520, 279383464, 273289130, 267332124, 261509143, 255816976, 250252495, 244812658, 239494505, 234295150]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 770).prefactor = (2433946841444229/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 770).cutoff/(generalMeanRows 770).c)).2 =
    (187672749752023/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 770).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 770).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 770).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 770

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 770).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 770).criticalRate j.val*(generalMeanRows 770).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 770).c*(generalMeanRows 770).criticalPoint j.val)).2-
      (generalMeanRows 770).J/2-(generalMeanRows 770).error (generalMeanGrid j.val)+
      (generalMeanRows 770).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 770).c)).2-
      (generalMeanRows 770).J/2-(generalMeanRows 770).error 4 := by
  have he : (generalMeanRows 770).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 770) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 770)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0770

/-! Kernel-checked entropy margins for general spectral rectangle 771. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0771
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5220063148, 5051561082, 4890497182, 4736443120, 4589001125, 4447801312, 4312499298, 4182774065, 4058326040, 3938875374, 3824160378, 3713936118, 3607973132, 3506056271, 3407983641, 3313565636, 3222624060, 3134991316, 3050509668, 2969030563, 2890414002, 2814527970, 2741247902, 2670456193, 2602041750, 2535899567, 2471930343, 2410040121, 2350139951, 2292145586, 2235977188, 2181559066, 2128819422, 2077690120, 2028106471, 1980007025, 1933333390, 1888030050, 1844044200, 1801325595, 1759826401, 1719501064, 1680306179, 1642200375, 1605144199, 1569100015, 1534031905, 1499905573, 1466688265, 1434348680, 1402856898, 1372184306, 1342303530, 1313188372, 1284813748, 1257155634, 1230191007, 1203897802, 1178254857, 1153241872, 1128839367, 1105028640, 1081791728, 1059111376, 1036970998, 1015354648, 994246988, 973633260, 953499262, 933831315, 914616247, 895841364, 877494432, 859563653, 842037649, 824905439, 808156428, 791780382, 775767420, 760107993, 744792873, 729813139, 715160163, 700825598, 686801369, 673079656, 659652889, 646513738, 633655097, 621070084, 608752026, 596694450, 584891083, 573335834, 562022794, 550946230, 540100571, 529480409, 519080491, 508895712, 498921112, 489151867, 479583288, 470210816, 461030013, 452036565, 443226270, 434595041, 426138897, 417853963, 409736463, 401782722, 393989156, 386352275, 378868676, 371535042, 364348141, 357304818, 350401998, 343636683, 337005944]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 771).prefactor = (2362063258535043/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 771).cutoff/(generalMeanRows 771).c)).2 =
    (415628280759493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 771).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 771).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 771).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 771

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 771).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 771).criticalRate j.val*(generalMeanRows 771).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 771).c*(generalMeanRows 771).criticalPoint j.val)).2-
      (generalMeanRows 771).J/2-(generalMeanRows 771).error (generalMeanGrid j.val)+
      (generalMeanRows 771).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 771).c)).2-
      (generalMeanRows 771).J/2-(generalMeanRows 771).error 4 := by
  have he : (generalMeanRows 771).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 771) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 771)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0771

/-! Kernel-checked entropy margins for general spectral rectangle 772. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0772
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5254147162, 5084544874, 4922429320, 4767369373, 4618964666, 4476842900, 4340657442, 4210085177, 4084824578, 3964593968, 3849129949, 3738185988, 3631531124, 3528948805, 3430235817, 3335201317, 3243665944, 3155461008, 3070427744, 2988416627, 2909286745, 2832905221, 2759146676, 2687892738, 2619031588, 2552457535, 2488070629, 2425776299, 2365485015, 2307111980, 2250576835, 2195803394, 2142719390, 2091256244, 2041348841, 1992935334, 1945956947, 1900357802, 1856084750, 1813087216, 1771317057, 1730728418, 1691277613, 1652923000, 1615624868, 1579345337, 1544048252, 1509699095, 1476264897, 1443714153, 1412016748, 1381143881, 1351068001, 1321762738, 1293202844, 1265364138, 1238223448, 1211758563, 1185948184, 1160771879, 1136210040, 1112243842, 1088855207, 1066026765, 1043741823, 1021984331, 1000738850, 979990526, 959725064, 939928697, 920588166, 901690694, 883223967, 865176110, 847535671, 830291598, 813433225, 796950253, 780832735, 765071061, 749655943, 734578400, 719829748, 705401587, 691285787, 677474479, 663960044, 650735101, 637792501, 625125315, 612726827, 600590523, 588710086, 577079387, 565692481, 554543592, 543627117, 532937612, 522469789, 512218509, 502178780, 492345748, 482714692, 473281022, 464040275, 454988104, 446120283, 437432697, 428921339, 420582309, 412411807, 404406132, 396561679, 388874933, 381342470, 373960953, 366727125, 359637813, 352689922, 345880433, 339206399]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 772).prefactor = (4754972349999099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 772).cutoff/(generalMeanRows 772).c)).2 =
    (415628280759493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 772).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 772).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 772).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 772

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 772).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 772).criticalRate j.val*(generalMeanRows 772).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 772).c*(generalMeanRows 772).criticalPoint j.val)).2-
      (generalMeanRows 772).J/2-(generalMeanRows 772).error (generalMeanGrid j.val)+
      (generalMeanRows 772).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 772).c)).2-
      (generalMeanRows 772).J/2-(generalMeanRows 772).error 4 := by
  have he : (generalMeanRows 772).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 772) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 772)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0772

/-! Kernel-checked entropy margins for general spectral rectangle 773. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0773
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5691109337, 5506145611, 5329268361, 5160020348, 4997976544, 4842741324, 4693945950, 4551246331, 4414321002, 4282869314, 4156609799, 4035278689, 3918628579, 3806427204, 3698456336, 3594510770, 3494397398, 3397934371, 3304950316, 3215283628, 3128781813, 3045300887, 2964704820, 2886865017, 2811659851, 2738974218, 2668699129, 2600731336, 2534972978, 2471331254, 2409718122, 2350050013, 2292247572, 2236235407, 2181941861, 2129298801, 2078241413, 2028708017, 1980639891, 1933981105, 1888678370, 1844680890, 1801940230, 1760410184, 1720046661, 1680807568, 1642652705, 1605543668, 1569443754, 1534317871, 1500132459, 1466855407, 1434455984, 1402904765, 1372173570, 1342235398, 1313064370, 1284635675, 1256925515, 1229911060, 1203570396, 1177882487, 1152827125, 1128384901, 1104537159, 1081265963, 1058554067, 1036384877, 1014742428, 993611349, 972976841, 952824646, 933141028, 913912748, 895127039, 876771592, 858834528, 841304384, 824170097, 807420982, 791046719, 775037337, 759383198, 744074986, 729103691, 714460599, 700137278, 686125566, 672417563, 659005617, 645882317, 633040484, 620473158, 608173593, 596135250, 584351783, 572817039, 561525046, 550470007, 539646297, 529048449, 518671159, 508509269, 498557770, 488811794, 479266607, 469917606, 460760316, 451790383, 443003571, 434395759, 425962935, 417701192, 409606730, 401675844, 393904927, 386290467, 378829039, 371517307, 364352019, 357330006]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 773).prefactor = (156933535511697/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 773).cutoff/(generalMeanRows 773).c)).2 =
    (388470216531341/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 773).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 773).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 773).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 773

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 773).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 773).criticalRate j.val*(generalMeanRows 773).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 773).c*(generalMeanRows 773).criticalPoint j.val)).2-
      (generalMeanRows 773).J/2-(generalMeanRows 773).error (generalMeanGrid j.val)+
      (generalMeanRows 773).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 773).c)).2-
      (generalMeanRows 773).J/2-(generalMeanRows 773).error 4 := by
  have he : (generalMeanRows 773).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 773) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 773)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0773

/-! Kernel-checked entropy margins for general spectral rectangle 774. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0774
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5175544566, 5006029506, 4843999868, 4689026935, 4540712455, 4398685985, 4262602511, 4132140322, 4006999099, 3886898195, 3771575085, 3660783958, 3554294450, 3451890480, 3353369203, 3258540049, 3167223840, 3079251992, 2994465776, 2912715641, 2833860595, 2757767628, 2684311186, 2613372684, 2544840056, 2478607334, 2414574265, 2352645954, 2292732527, 2234748829, 2178614128, 2124251857, 2071589357, 2020557650, 1971091223, 1923127821, 1876608264, 1831476266, 1787678275, 1745163314, 1703882837, 1663790597, 1624842515, 1586996565, 1550212658, 1514452538, 1479679687, 1445859228, 1412957840, 1380943677, 1349786289, 1319456548, 1289926585, 1261169721, 1233160408, 1205874172, 1179287558, 1153378080, 1128124173, 1103505147, 1079501145, 1056093103, 1033262709, 1010992369, 989265175, 968064867, 947375809, 927182952, 907471817, 888228459, 869439449, 851091847, 833173182, 815671430, 798574996, 781872691, 765553720, 749607658, 734024441, 718794346, 703907978, 689356255, 675130397, 661221912, 647622584, 634324464, 621319854, 608601304, 596161595, 583993736, 572090949, 560446667, 549054522, 537908335, 527002117, 516330053, 505886500, 495665980, 485663174, 475872916, 466290187, 456910109, 447727943, 438739082, 429939046, 421323476, 412888135, 404628901, 396541759, 388622806, 380868240, 373274358, 365837557, 358554326, 351421245, 344434981, 337592287, 330889999, 324325032, 317894378, 311595103]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 774).prefactor = (473455126591647/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 774).cutoff/(generalMeanRows 774).c)).2 =
    (100674996279687/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 774).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 774).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 774).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 774

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 774).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 774).criticalRate j.val*(generalMeanRows 774).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 774).c*(generalMeanRows 774).criticalPoint j.val)).2-
      (generalMeanRows 774).J/2-(generalMeanRows 774).error (generalMeanGrid j.val)+
      (generalMeanRows 774).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 774).c)).2-
      (generalMeanRows 774).J/2-(generalMeanRows 774).error 4 := by
  have he : (generalMeanRows 774).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 774) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 774)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0774

/-! Kernel-checked entropy margins for general spectral rectangle 775. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0775
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5506721830, 5320191384, 5141876506, 4971315749, 4808080006, 4651769685, 4502012196, 4358459694, 4220787058, 4088690078, 3961883812, 3840101103, 3723091241, 3610618734, 3502462208, 3398413384, 3298276161, 3201865764, 3109007967, 3019538384, 2933301808, 2850151610, 2769949181, 2692563415, 2617870236, 2545752156, 2476097866, 2408801858, 2343764071, 2280889566, 2220088220, 2161274442, 2104366909, 2049288320, 1995965162, 1944327500, 1894308770, 1845845595, 1798877604, 1753347272, 1709199758, 1666382767, 1624846407, 1584543064, 1545427281, 1507455644, 1470586674, 1434780731, 1399999914, 1366207974, 1333370234, 1301453501, 1270426001, 1240257301, 1210918248, 1182380903, 1154618481, 1127605297, 1101316713, 1075729087, 1050819724, 1026566835, 1002949490, 979947582, 957541785, 935713521, 914444923, 893718805, 873518630, 853828481, 834633032, 815917523, 797667737, 779869972, 762511021, 745578149, 729059076, 712941954, 697215349, 681868227, 666889931, 652270173, 637999012, 624066842, 610464381, 597182653, 584212979, 571546966, 559176491, 547093695, 535290970, 523760952, 512496506, 501490724, 490736911, 480228581, 469959445, 459923408, 450114558, 440527161, 431155654, 421994641, 413038882, 404283293, 395722937, 387353020, 379168884, 371166006, 363339990, 355686565, 348201578, 340880993, 333720884, 326717436, 319866935, 313165770, 306610427, 300197485, 293923617, 287785583, 281780229]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 775).prefactor = (1267973539292731/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 775).cutoff/(generalMeanRows 775).c)).2 =
    (360510176588411/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 775).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 775).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 775).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 775

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 775).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 775).criticalRate j.val*(generalMeanRows 775).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 775).c*(generalMeanRows 775).criticalPoint j.val)).2-
      (generalMeanRows 775).J/2-(generalMeanRows 775).error (generalMeanGrid j.val)+
      (generalMeanRows 775).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 775).c)).2-
      (generalMeanRows 775).J/2-(generalMeanRows 775).error 4 := by
  have he : (generalMeanRows 775).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 775) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 775)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0775

/-! Kernel-checked entropy margins for general spectral rectangle 776. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0776
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5001025365, 4830294396, 4667165360, 4511205711, 4362013468, 4219214552, 4082460398, 3951425829, 3825807139, 3705320374, 3589699775, 3478696376, 3372076725, 3269621731, 3171125604, 3076394901, 2985247639, 2897512498, 2813028078, 2731642225, 2653211407, 2577600140, 2504680462, 2434331439, 2366438720, 2300894113, 2237595203, 2176444991, 2117351559, 2060227763, 2004990942, 1951562654, 1899868423, 1849837504, 1801402672, 1754500013, 1709068736, 1665050998, 1622391736, 1581038509, 1540941358, 1502052667, 1464327031, 1427721144, 1392193678, 1357705184, 1324217987, 1291696094, 1260105110, 1229412148, 1199585758, 1170595846, 1142413612, 1115011482, 1088363043, 1062442991, 1037227071, 1012692028, 988815557, 965576259, 942953595, 920927842, 899480063, 878592059, 858246344, 838426104, 819115172, 800297991, 781959596, 764085577, 746662061, 729675685, 713113572, 696963313, 681212945, 665850929, 650866137, 636247828, 621985637, 608069555, 594489918, 581237387, 568302941, 555677859, 543353710, 531322341, 519575864, 508106648, 496907308, 485970695, 475289886, 464858175, 454669068, 444716270, 434993682, 425495391, 416215661, 407148933, 398289812, 389633063, 381173607, 372906515, 364826997, 356930408, 349212231, 341668081, 334293699, 327084941, 320037785, 313148317, 306412734, 299827336, 293388525, 287092802, 280936761, 274917089, 269030561, 263274038, 257644464, 252138864, 246754341]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 776).prefactor = (955434250147611/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 776).cutoff/(generalMeanRows 776).c)).2 =
    (75093488657623/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 776).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 776).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 776).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 776

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 776).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 776).criticalRate j.val*(generalMeanRows 776).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 776).c*(generalMeanRows 776).criticalPoint j.val)).2-
      (generalMeanRows 776).J/2-(generalMeanRows 776).error (generalMeanGrid j.val)+
      (generalMeanRows 776).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 776).c)).2-
      (generalMeanRows 776).J/2-(generalMeanRows 776).error 4 := by
  have he : (generalMeanRows 776).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 776) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 776)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0776

/-! Kernel-checked entropy margins for general spectral rectangle 777. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0777
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5124316246, 4954078334, 4791385993, 4635807438, 4486941542, 4344415154, 4207880711, 4077014096, 3951512720, 3831093789, 3715492743, 3604461848, 3497768910, 3395196115, 3296538970, 3201605334, 3110214541, 3022196582, 2937391376, 2855648078, 2776824463, 2700786343, 2627407040, 2556566892, 2488152803, 2422057822, 2358180754, 2296425801, 2236702225, 2178924041, 2123009725, 2068881947, 2016467317, 1965696159, 1916502285, 1868822795, 1822597891, 1777770691, 1734287072, 1692095508, 1651146926, 1611394574, 1572793885, 1535302367, 1498879480, 1463486539, 1429086610, 1395644418, 1363126260, 1331499920, 1300734596, 1270800820, 1241670397, 1213316334, 1185712782, 1158834977, 1132659187, 1107162659, 1082323572, 1058120990, 1034534819, 1011545769, 989135311, 967285642, 945979653, 925200895, 904933544, 885162380, 865872750, 847050551, 828682197, 810754602, 793255151, 776171687, 759492484, 743206230, 727302010, 711769290, 696597895, 681778001, 667300115, 653155063, 639333975, 625828276, 612629671, 599730133, 587121894, 574797435, 562749474, 550970957, 539455051, 528195133, 517184784, 506417779, 495888083, 485589838, 475517363, 465665144, 456027826, 446600213, 437377255, 428354050, 419525832, 410887972, 402435968, 394165446, 386072150, 378151943, 370400799, 362814801, 355390138, 348123101, 341010079, 334047555, 327232106, 320560398, 314029181, 307635292, 301375647, 295247241, 289247144]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 777).prefactor = (190638860952533/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 777).cutoff/(generalMeanRows 777).c)).2 =
    (395427225789669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 777).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 777).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 777).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 777

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 777).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 777).criticalRate j.val*(generalMeanRows 777).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 777).c*(generalMeanRows 777).criticalPoint j.val)).2-
      (generalMeanRows 777).J/2-(generalMeanRows 777).error (generalMeanGrid j.val)+
      (generalMeanRows 777).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 777).c)).2-
      (generalMeanRows 777).J/2-(generalMeanRows 777).error 4 := by
  have he : (generalMeanRows 777).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 777) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 777)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0777

/-! Kernel-checked entropy margins for general spectral rectangle 778. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0778
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5158323131, 4986955456, 4823183427, 4666572395, 4516718569, 4373246322, 4235805785, 4104070691, 3977736441, 3856518364, 3740150147, 3628382409, 3520981416, 3417727909, 3318416038, 3222852388, 3130855091, 3042253012, 2956885007, 2874599230, 2795252512, 2718709774, 2644843498, 2573533229, 2504665118, 2438131506, 2373830526, 2311665744, 2251545820, 2193384199, 2137098814, 2082611823, 2029849351, 1978741256, 1929220912, 1881225004, 1834693334, 1789568644, 1745796452, 1703324888, 1662104556, 1622088392, 1583231535, 1545491209, 1508826606, 1473198785, 1438570565, 1404906438, 1372172477, 1340336253, 1309366758, 1279234331, 1249910587, 1221368356, 1193581616, 1166525440, 1140175938, 1114510206, 1089506277, 1065143077, 1041400380, 1018258766, 995699583, 973704912, 952257529, 931340875, 910939023, 891036649, 871619007, 852671896, 834181643, 816135073, 798519490, 781322654, 764532761, 748138425, 732128659, 716492858, 701220780, 686302536, 671728569, 657489645, 643576835, 629981507, 616695311, 603710167, 591018255, 578612007, 566484090, 554627407, 543035077, 531700434, 520617016, 509778558, 499178982, 488812394, 478673075, 468755472, 459054198, 449564019, 440279855, 431196768, 422309963, 413614779, 405106684, 396781276, 388634270, 380661501, 372858917, 365222576, 357748641, 350433377, 343273150, 336264420, 329403741, 322687757, 316113197, 309676876, 303375689, 297206612, 291166696]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 778).prefactor = (959520059665153/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 778).cutoff/(generalMeanRows 778).c)).2 =
    (395427225789669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 778).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 778).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 778).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 778

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 778).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 778).criticalRate j.val*(generalMeanRows 778).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 778).c*(generalMeanRows 778).criticalPoint j.val)).2-
      (generalMeanRows 778).J/2-(generalMeanRows 778).error (generalMeanGrid j.val)+
      (generalMeanRows 778).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 778).c)).2-
      (generalMeanRows 778).J/2-(generalMeanRows 778).error 4 := by
  have he : (generalMeanRows 778).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 778) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 778)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0778

/-! Kernel-checked entropy margins for general spectral rectangle 779. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0779
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5034764256, 4862881469, 4698651900, 4541640085, 4391441333, 4247679039, 4110002288, 3978083708, 3851617544, 3730317928, 3613917307, 3502165035, 3394826086, 3291679890, 3192519270, 3097149475, 3005387298, 2917060261, 2832005876, 2750070962, 2671111018, 2594989649, 2521578025, 2450754400, 2382403650, 2316416853, 2252690904, 2191128148, 2131636049, 2074126872, 2018517403, 1964728667, 1912685685, 1862317238, 1813555646, 1766336562, 1720598788, 1676284090, 1633337031, 1591704819, 1551337157, 1512186107, 1474205960, 1437353114, 1401585967, 1366864799, 1333151684, 1300410386, 1268606277, 1237706248, 1207678637, 1178493148, 1150120786, 1122533790, 1095705570, 1069610651, 1044224614, 1019524048, 995486497, 972090418, 949315132, 927140785, 905548310, 884519388, 864036413, 844082458, 824641246, 805697118, 787235004, 769240400, 751699338, 734598365, 717924517, 701665303, 685808676, 670343023, 655257137, 640540207, 626181798, 612171833, 598500581, 585158644, 572136937, 559426681, 547019389, 534906851, 523081127, 511534536, 500259641, 489249245, 478496379, 467994292, 457736445, 447716502, 437928321, 428365950, 419023616, 409895721, 400976832, 392261682, 383745155, 375422289, 367288264, 359338401, 351568154, 343973109, 336548976, 329291585, 322196886, 315260939, 308479915, 301850090, 295367840, 289029644, 282832072, 276771788, 270845547, 265050188, 259382635, 253839892, 248419043]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 779).prefactor = (2404699966960093/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 779).cutoff/(generalMeanRows 779).c)).2 =
    (75093488657623/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 779).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 779).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 779).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 779

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 779).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 779).criticalRate j.val*(generalMeanRows 779).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 779).c*(generalMeanRows 779).criticalPoint j.val)).2-
      (generalMeanRows 779).J/2-(generalMeanRows 779).error (generalMeanGrid j.val)+
      (generalMeanRows 779).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 779).c)).2-
      (generalMeanRows 779).J/2-(generalMeanRows 779).error 4 := by
  have he : (generalMeanRows 779).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 779) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 779)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0779

/-! Kernel-checked entropy margins for general spectral rectangle 780. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0780
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4987011445, 4814474945, 4649652332, 4492104905, 4341424933, 4197232957, 4059175373, 3926922274, 3800165516, 3678616968, 3562006943, 3450082771, 3342607511, 3239358773, 3140127657, 3044717774, 2952944359, 2864633451, 2779621154, 2697752945, 2618883044, 2542873834, 2469595327, 2398924663, 2330745661, 2264948388, 2201428773, 2140088237, 2080833362, 2023575571, 1968230840, 1914719427, 1862965612, 1812897470, 1764446644, 1717548143, 1672140147, 1628163829, 1585563186, 1544284880, 1504278095, 1465494394, 1427887590, 1391413625, 1356030457, 1321697950, 1288377773, 1256033308, 1224629557, 1194133062, 1164511821, 1135735216, 1107773943, 1080599947, 1054186354, 1028507420, 1003538467, 979255836, 955636838, 932659702, 910303534, 888548276, 867374664, 846764191, 826699074, 807162215, 788137176, 769608143, 751559900, 733977803, 716847750, 700156164, 683889960, 668036533, 652583730, 637519835, 622833545, 608513958, 594550551, 580933169, 567652003, 554697583, 542060756, 529732680, 517704808, 505968876, 494516892, 483341126, 472434096, 461788565, 451397524, 441254187, 431351985, 421684551, 412245717, 403029506, 394030124, 385241952, 376659544, 368277615, 360091039, 352094841, 344284195, 336654413, 329200946, 321919375, 314805409, 307854881, 301063738, 294428046, 287943979, 281607819, 275415950, 269364857, 263451122, 257671418, 252022510, 246501251, 241104577, 235829508, 230673142]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 780).prefactor = (2420923022261127/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 780).cutoff/(generalMeanRows 780).c)).2 =
    (368349975519251/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 780).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 780).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 780).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 780

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 780).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 780).criticalRate j.val*(generalMeanRows 780).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 780).c*(generalMeanRows 780).criticalPoint j.val)).2-
      (generalMeanRows 780).J/2-(generalMeanRows 780).error (generalMeanGrid j.val)+
      (generalMeanRows 780).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 780).c)).2-
      (generalMeanRows 780).J/2-(generalMeanRows 780).error 4 := by
  have he : (generalMeanRows 780).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 780) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 780)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0780

/-! Kernel-checked entropy margins for general spectral rectangle 781. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0781
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5063839741, 4893221975, 4730220864, 4574398990, 4425350046, 4282696119, 4146085260, 4015189317, 3889701978, 3769337023, 3653826731, 3542920449, 3436383294, 3333994966, 3235548679, 3140850172, 3049716817, 2961976797, 2877468353, 2796039093, 2717545355, 2641851625, 2568829995, 2498359665, 2430326482, 2364622518, 2301145669, 2239799296, 2180491880, 2123136710, 2067651590, 2013958562, 1961983657, 1911656656, 1862910870, 1815682930, 1769912600, 1725542595, 1682518412, 1640788172, 1600302475, 1561014259, 1522878672, 1485852953, 1449896313, 1414969831, 1381036356, 1348060406, 1316008086, 1284847001, 1254546179, 1225075996, 1196408106, 1168515377, 1141371830, 1114952577, 1089233770, 1064192549, 1039806988, 1016056056, 992919569, 970378150, 948413191, 927006813, 906141836, 885801742, 865970646, 846633267, 827774898, 809381382, 791439083, 773934868, 756856080, 740190519, 723926422, 708052440, 692557624, 677431408, 662663589, 648244315, 634164066, 620413645, 606984161, 593867018, 581053902, 568536769, 556307836, 544359570, 532684675, 521276088, 510126964, 499230672, 488580785, 478171073, 467995494, 458048187, 448323468, 438815819, 429519888, 420430474, 411542533, 402851160, 394351595, 386039211, 377909511, 369958126, 362180806, 354573419, 347131948, 339852485, 332731226, 325764472, 318948621, 312280168, 305755701, 299371897, 293125519, 287013417, 281032520, 275179836, 269452451]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 781).prefactor = (192690781905579/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 781).cutoff/(generalMeanRows 781).c)).2 =
    (98452308341213/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 781).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 781).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 781).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 781

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 781).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 781).criticalRate j.val*(generalMeanRows 781).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 781).c*(generalMeanRows 781).criticalPoint j.val)).2-
      (generalMeanRows 781).J/2-(generalMeanRows 781).error (generalMeanGrid j.val)+
      (generalMeanRows 781).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 781).c)).2-
      (generalMeanRows 781).J/2-(generalMeanRows 781).error 4 := by
  have he : (generalMeanRows 781).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 781) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 781)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0781

/-! Kernel-checked entropy margins for general spectral rectangle 782. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0782
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5130183560, 4957330448, 4792193780, 4634330408, 4483328702, 4338805797, 4200405133, 4067794258, 3940662850, 3818720935, 3701697286, 3589337967, 3481405017, 3377675251, 3277939171, 3181999972, 3089672635, 3000783091, 2915167461, 2832671356, 2753149234, 2676463804, 2602485482, 2531091886, 2462167368, 2395602584, 2331294094, 2269143992, 2209059561, 2150952953, 2094740895, 2040344409, 1987688556, 1936702197, 1887317768, 1839471072, 1793101083, 1748149765, 1704561902, 1662284934, 1621268813, 1581465863, 1542830644, 1505319833, 1468892107, 1433508037, 1399129982, 1365721999, 1333249746, 1301680405, 1270982597, 1241126310, 1212082828, 1183824663, 1156325495, 1129560111, 1103504350, 1078135051, 1053430003, 1029367899, 1005928289, 983091545, 960838811, 939151978, 918013639, 897407060, 877316147, 857725420, 838619979, 819985479, 801808110, 784074563, 766772018, 749888114, 733410933, 717328978, 701631157, 686306766, 671345466, 656737278, 642472557, 628541985, 614936555, 601647557, 588666570, 575985445, 563596295, 551491489, 539663636, 528105579, 516810384, 505771335, 494981919, 484435824, 474126930, 464049298, 454197171, 444564958, 435147236, 425938738, 416934351, 408129108, 399518187, 391096898, 382860687, 374805127, 366925912, 359218857, 351679892, 344305057, 337090499, 330032470, 323127321, 316371502, 309761555, 303294113, 296965899, 290773719, 284714463, 278785100, 272982678]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 782).prefactor = (4880382931063529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 782).cutoff/(generalMeanRows 782).c)).2 =
    (98452308341213/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 782).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 782).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 782).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 782

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 782).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 782).criticalRate j.val*(generalMeanRows 782).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 782).c*(generalMeanRows 782).criticalPoint j.val)).2-
      (generalMeanRows 782).J/2-(generalMeanRows 782).error (generalMeanGrid j.val)+
      (generalMeanRows 782).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 782).c)).2-
      (generalMeanRows 782).J/2-(generalMeanRows 782).error 4 := by
  have he : (generalMeanRows 782).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 782) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 782)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0782

/-! Kernel-checked entropy margins for general spectral rectangle 783. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0783
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5197018832, 5028258429, 4866938165, 4712630590, 4564938721, 4423493384, 4287950833, 4157990622, 4033313687, 3913640633, 3798710171, 3688277718, 3582114121, 3480004496, 3381747176, 3287152748, 3196043174, 3108250988, 3023618555, 2941997396, 2863247566, 2787237078, 2713841376, 2642942848, 2574430373, 2508198904, 2444149085, 2382186888, 2322223283, 2264173930, 2207958891, 2153502363, 2100732428, 2049580826, 1999982733, 1951876564, 1905203781, 1859908720, 1815938426, 1773242497, 1731772942, 1691484047, 1652332244, 1614275998, 1577275693, 1541293525, 1506293410, 1472240887, 1439103034, 1406848384, 1375446854, 1344869663, 1315089277, 1286079333, 1257814587, 1230270855, 1203424958, 1177254672, 1151738683, 1126856539, 1102588609, 1078916043, 1055820734, 1033285282, 1011292961, 989827686, 968873983, 948416962, 928442288, 908936156, 889885266, 871276803, 853098410, 835338172, 817984597, 801026590, 784453446, 768254824, 752420738, 736941535, 721807890, 707010783, 692541492, 678391577, 664552872, 651017472, 637777721, 624826205, 612155741, 599759366, 587630332, 575762094, 564148305, 552782807, 541659625, 530772957, 520117173, 509686803, 499476536, 489481208, 479695806, 470115452, 460735407, 451551060, 442557929, 433751651, 425127981, 416682789, 408412053, 400311859, 392378393, 384607943, 376996892, 369541714, 362238976, 355085330, 348077512, 341212343, 334486720, 327897617, 321442084]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 783).prefactor = (4745994540270049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 783).cutoff/(generalMeanRows 783).c)).2 =
    (205466076430199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 783).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 783).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 783).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 783

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 783).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 783).criticalRate j.val*(generalMeanRows 783).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 783).c*(generalMeanRows 783).criticalPoint j.val)).2-
      (generalMeanRows 783).J/2-(generalMeanRows 783).error (generalMeanGrid j.val)+
      (generalMeanRows 783).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 783).c)).2-
      (generalMeanRows 783).J/2-(generalMeanRows 783).error 4 := by
  have he : (generalMeanRows 783).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 783) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 783)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0783

/-! Kernel-checked entropy margins for general spectral rectangle 784. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0784
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5264813110, 5093851254, 4930426594, 4774106100, 4624487614, 4481197146, 4343886464, 4212230943, 4085927618, 3964693447, 3848263736, 3736390710, 3628842226, 3525400597, 3425861526, 3330033128, 3237735045, 3148797624, 3063061174, 2980375281, 2900598172, 2823596139, 2749243002, 2677419614, 2608013404, 2540917957, 2476032618, 2413262134, 2352516314, 2293709716, 2236761361, 2181594456, 2128136146, 2076317279, 2026072187, 1977338481, 1930056859, 1884170931, 1839627052, 1796374161, 1754363643, 1713549185, 1673886654, 1635333970, 1597851001, 1561399452, 1525942766, 1491446033, 1457875902, 1425200496, 1393389337, 1362413272, 1332244405, 1302856032, 1274222577, 1246319542, 1219123444, 1192611771, 1166762930, 1141556202, 1116971701, 1092990330, 1069593746, 1046764323, 1024485115, 1002739829, 981512789, 960788909, 940553669, 920793082, 901493677, 882642469, 864226942, 846235025, 828655075, 811475854, 794686515, 778276585, 762235945, 746554820, 731223759, 716233626, 701575584, 687241086, 673221857, 659509890, 646097429, 632976963, 620141215, 607583131, 595295876, 583272818, 571507529, 559993770, 548725488, 537696805, 526902018, 516335586, 505992127, 495866412, 485953361, 476248033, 466745626, 457441472, 448331026, 439409871, 430673707, 422118349, 413739723, 405533863, 397496906, 389625092, 381914756, 374362326, 366964325, 359717361, 352618128, 345663404, 338850045, 332174989, 325635244]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 784).prefactor = (4807905278255321/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 784).cutoff/(generalMeanRows 784).c)).2 =
    (205466076430199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 784).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 784).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 784).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 784

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 784).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 784).criticalRate j.val*(generalMeanRows 784).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 784).c*(generalMeanRows 784).criticalPoint j.val)).2-
      (generalMeanRows 784).J/2-(generalMeanRows 784).error (generalMeanGrid j.val)+
      (generalMeanRows 784).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 784).c)).2-
      (generalMeanRows 784).J/2-(generalMeanRows 784).error 4 := by
  have he : (generalMeanRows 784).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 784) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 784)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0784

/-! Kernel-checked entropy margins for general spectral rectangle 785. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0785
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5076209207, 4904290552, 4740039586, 4583016867, 4432814182, 4289051818, 4151376129, 4019457350, 3892987645, 3771679341, 3655263338, 3543487668, 3436116190, 3332927408, 3233713383, 3138278757, 3046439846, 2958023821, 2872867948, 2790818899, 2711732112, 2635471202, 2561907425, 2490919170, 2422391506, 2356215749, 2292289067, 2230514114, 2170798691, 2113055425, 2057201478, 2003158275, 1950851244, 1900209584, 1851166039, 1803656693, 1757620779, 1713000493, 1669740832, 1627789431, 1587096414, 1547614264, 1509297681, 1472103470, 1435990422, 1400919208, 1366852277, 1333753764, 1301589398, 1270326418, 1239933498, 1210380670, 1181639254, 1153681792, 1126481989, 1100014652, 1074255632, 1049181779, 1024770887, 1001001651, 977853621, 955307162, 933343414, 911944255, 891092269, 870770708, 850963464, 831655039, 812830516, 794475532, 776576256, 759119362, 742092006, 725481807, 709276825, 693465542, 678036846, 662980008, 648284671, 633940831, 619938824, 606269311, 592923265, 579891956, 567166942, 554740055, 542603391, 530749301, 519170376, 507859443, 496809553, 486013972, 475466174, 465159834, 455088818, 445247175, 435629135, 426229098, 417041630, 408061455, 399283450, 390702643, 382314200, 374113429, 366095769, 358256786, 350592172, 343097738, 335769409, 328603225, 321595330, 314741975, 308039512, 301484390, 295073151, 288802432, 282668956, 276669532, 270801052, 265060491, 259444899]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 785).prefactor = (4870623631893199/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 785).cutoff/(generalMeanRows 785).c)).2 =
    (389502761404499/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 785).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 785).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 785).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 785

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 785).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 785).criticalRate j.val*(generalMeanRows 785).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 785).c*(generalMeanRows 785).criticalPoint j.val)).2-
      (generalMeanRows 785).J/2-(generalMeanRows 785).error (generalMeanGrid j.val)+
      (generalMeanRows 785).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 785).c)).2-
      (generalMeanRows 785).J/2-(generalMeanRows 785).error 4 := by
  have he : (generalMeanRows 785).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 785) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 785)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0785

/-! Kernel-checked entropy margins for general spectral rectangle 786. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0786
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7647669781, 7425831787, 7212745992, 7007956324, 6811038049, 6621594943, 6439256787, 6263677139, 6094531345, 5931514770, 5774341202, 5622741421, 5476461909, 5335263682, 5198921232, 5067221567, 4939963334, 4816956026, 4698019247, 4582982047, 4471682307, 4363966179, 4259687561, 4158707625, 4060894370, 3966122215, 3874271619, 3785228733, 3698885069, 3615137198, 3533886468, 3455038739, 3378504140, 3304196835, 3232034810, 3161939673, 3093836463, 3027653474, 2963322091, 2900776631, 2839954198, 2780794544, 2723239939, 2667235051, 2612726828, 2559664387, 2507998918, 2457683578, 2408673406, 2360925233, 2314397598, 2269050674, 2224846192, 2181747369, 2139718847, 2098726623, 2058737993, 2019721498, 1981646863, 1944484950, 1908207709, 1872788132, 1838200206, 1804418873, 1771419990, 1739180290, 1707677346, 1676889536, 1646796010, 1617376658, 1588612082, 1560483563, 1532973039, 1506063073, 1479736832, 1453978063, 1428771067, 1404100681, 1379952253, 1356311626, 1333165117, 1310499496, 1288301975, 1266560185, 1245262163, 1224396336, 1203951506, 1183916836, 1164281836, 1145036353, 1126170553, 1107674914, 1089540212, 1071757512, 1054318155, 1037213751, 1020436164, 1003977511, 987830144, 971986649, 956439833, 941182718, 926208533, 911510706, 897082860, 882918801, 869012518, 855358170, 841950087, 828782757, 815850827, 803149093, 790672499, 778416127, 766375198, 754545061, 742921196, 731499204, 720274804, 709243833, 698402236]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 786).prefactor = (5030635125419257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 786).cutoff/(generalMeanRows 786).c)).2 =
    (78801587499581/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 786).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 786).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 786).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 786

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 786).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 786).criticalRate j.val*(generalMeanRows 786).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 786).c*(generalMeanRows 786).criticalPoint j.val)).2-
      (generalMeanRows 786).J/2-(generalMeanRows 786).error (generalMeanGrid j.val)+
      (generalMeanRows 786).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 786).c)).2-
      (generalMeanRows 786).J/2-(generalMeanRows 786).error 4 := by
  have he : (generalMeanRows 786).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 786) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 786)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0786

/-! Kernel-checked entropy margins for general spectral rectangle 787. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0787
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7024446105, 6824921796, 6633407854, 6449478691, 6272738023, 6102816248, 5939368130, 5782070733, 5630621577, 5484736984, 5344150599, 5208612048, 5077885737, 4951749754, 4829994882, 4712423694, 4598849731, 4489096752, 4382998047, 4280395806, 4181140541, 4085090552, 3992111439, 3902075645, 3814862041, 3730355536, 3648446718, 3569031523, 3492010920, 3417290628, 3344780843, 3274395992, 3206054493, 3139678544, 3075193912, 3012529745, 2951618392, 2892395235, 2834798533, 2778769268, 2724251013, 2671189795, 2619533976, 2569234134, 2520242953, 2472515123, 2426007239, 2380677709, 2336486671, 2293395906, 2251368762, 2210370080, 2170366126, 2131324523, 2093214187, 2056005274, 2019669116, 1984178171, 1949505973, 1915627085, 1882517048, 1850152343, 1818510348, 1787569298, 1757308246, 1727707034, 1698746250, 1670407204, 1642671891, 1615522967, 1588943717, 1562918032, 1537430380, 1512465785, 1488009803, 1464048497, 1440568424, 1417556604, 1395000512, 1372888052, 1351207541, 1329947695, 1309097613, 1288646757, 1268584943, 1248902326, 1229589382, 1210636903, 1192035979, 1173777987, 1155854584, 1138257691, 1120979486, 1104012395, 1087349078, 1070982426, 1054905548, 1039111765, 1023594603, 1008347781, 993365209, 978640978, 964169355, 949944774, 935961835, 922215290, 908700048, 895411159, 882343816, 869493347, 856855211, 844424995, 832198405, 820171267, 808339519, 796699210, 785246495, 773977630, 762888973, 751976974, 741238178]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 787).prefactor = (2349218604674089/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 787).cutoff/(generalMeanRows 787).c)).2 =
    (356978941509107/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 787).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 787).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 787).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 787

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 787).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 787).criticalRate j.val*(generalMeanRows 787).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 787).c*(generalMeanRows 787).criticalPoint j.val)).2-
      (generalMeanRows 787).J/2-(generalMeanRows 787).error (generalMeanGrid j.val)+
      (generalMeanRows 787).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 787).c)).2-
      (generalMeanRows 787).J/2-(generalMeanRows 787).error 4 := by
  have he : (generalMeanRows 787).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 787) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 787)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0787

/-! Kernel-checked entropy margins for general spectral rectangle 788. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0788
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6871619249, 6663814040, 6464419460, 6272991027, 6089114784, 5912404570, 5742499610, 5579062361, 5421776589, 5270345652, 5124490953, 4983950549, 4848477894, 4717840700, 4591819906, 4470208736, 4352811846, 4239444542, 4129932062, 4024108922, 3921818310, 3822911538, 3727247525, 3634692330, 3545118711, 3458405726, 3374438360, 3293107171, 3214307974, 3137941541, 3063913315, 2992133156, 2922515095, 2854977108, 2789440899, 2725831708, 2664078118, 2604111883, 2545867765, 2489283376, 2434299036, 2380857636, 2328904509, 2278387310, 2229255901, 2181462242, 2134960293, 2089705915, 2045656783, 2002772294, 1961013494, 1920342994, 1880724903, 1842124754, 1804509444, 1767847169, 1732107365, 1697260655, 1663278794, 1630134618, 1597802001, 1566255802, 1535471830, 1505426797, 1476098283, 1447464696, 1419505238, 1392199871, 1365529287, 1339474873, 1314018686, 1289143424, 1264832398, 1241069509, 1217839224, 1195126549, 1172917013, 1151196643, 1129951944, 1109169882, 1088837865, 1068943725, 1049475699, 1030422420, 1011772895, 993516491, 975642924, 958142247, 941004830, 924221355, 907782802, 891680436, 875905797, 860450692, 845307183, 830467577, 815924419, 801670481, 787698758, 774002452, 760574973, 747409926, 734501107, 721842495, 709428245, 697252682, 685310296, 673595736, 662103802, 650829446, 639767758, 628913968, 618263440, 607811665, 597554259, 587486957, 577605613, 567906190, 558384760, 549037502, 539860695]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 788).prefactor = (981912791487513/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 788).cutoff/(generalMeanRows 788).c)).2 =
    (32126085890703/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 788).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 788).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 788).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 788

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 788).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 788).criticalRate j.val*(generalMeanRows 788).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 788).c*(generalMeanRows 788).criticalPoint j.val)).2-
      (generalMeanRows 788).J/2-(generalMeanRows 788).error (generalMeanGrid j.val)+
      (generalMeanRows 788).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 788).c)).2-
      (generalMeanRows 788).J/2-(generalMeanRows 788).error 4 := by
  have he : (generalMeanRows 788).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 788) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 788)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0788

/-! Kernel-checked entropy margins for general spectral rectangle 789. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0789
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6683681768, 6483569045, 6291622663, 6107406414, 5930514121, 5760566968, 5597211136, 5440115691, 5288970702, 5143485550, 5003387410, 4868419880, 4738341745, 4612925857, 4491958116, 4375236541, 4262570431, 4153779587, 4048693610, 3947151246, 3848999799, 3754094575, 3662298379, 3573481050, 3487519027, 3404294950, 3323697290, 3245620006, 3169962222, 3096627933, 3025525728, 2956568530, 2889673354, 2824761083, 2761756260, 2700586886, 2641184237, 2583482691, 2527419567, 2472934969, 2419971646, 2368474851, 2318392223, 2269673660, 2222271209, 2176138958, 2131232940, 2087511034, 2044932877, 2003459779, 1963054645, 1923681897, 1885307404, 1847898415, 1811423491, 1775852451, 1741156307, 1707307213, 1674278416, 1642044201, 1610579847, 1579861584, 1549866549, 1520572747, 1491959011, 1464004969, 1436691006, 1409998234, 1383908461, 1358404157, 1333468431, 1309085002, 1285238172, 1261912803, 1239094293, 1216768556, 1194921997, 1173541493, 1152614377, 1132128414, 1112071788, 1092433083, 1073201267, 1054365678, 1035916008, 1017842289, 1000134880, 982784454, 965781988, 949118747, 932786276, 916776389, 901081157, 885692899, 870604176, 855807775, 841296707, 827064196, 813103670, 799408755, 785973268, 772791210, 759856757, 747164257, 734708222, 722483322, 710484381, 698706369, 687144399, 675793722, 664649719, 653707901, 642963903, 632413478, 622052495, 611876933, 601882881, 592066530, 582424172, 572952197, 563647088]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 789).prefactor = (4822338861335447/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 789).cutoff/(generalMeanRows 789).c)).2 =
    (343089829348441/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 789).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 789).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 789).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 789

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 789).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 789).criticalRate j.val*(generalMeanRows 789).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 789).c*(generalMeanRows 789).criticalPoint j.val)).2-
      (generalMeanRows 789).J/2-(generalMeanRows 789).error (generalMeanGrid j.val)+
      (generalMeanRows 789).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 789).c)).2-
      (generalMeanRows 789).J/2-(generalMeanRows 789).error 4 := by
  have he : (generalMeanRows 789).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 789) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 789)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0789

/-! Kernel-checked entropy margins for general spectral rectangle 790. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0790
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6390284094, 6198622134, 6014861783, 5838576444, 5669368980, 5506869109, 5350731088, 5200631653, 5056268172, 4917356991, 4783631945, 4654843013, 4530755102, 4411146949, 4295810116, 4184548083, 4077175411, 3973516985, 3873407319, 3776689912, 3683216664, 3592847335, 3505449044, 3420895810, 3339068126, 3259852565, 3183141412, 3108832327, 3036828027, 2967035994, 2899368203, 2833740863, 2770074181, 2708292141, 2648322292, 2590095560, 2533546059, 2478610922, 2425230144, 2373346427, 2322905041, 2273853692, 2226142395, 2179723355, 2134550860, 2090581175, 2047772441, 2006084586, 1965479234, 1925919623, 1887370529, 1849798189, 1813170233, 1777455615, 1742624553, 1708648470, 1675499936, 1643152613, 1611581211, 1580761432, 1550669931, 1521284268, 1492582870, 1464544992, 1437150680, 1410380734, 1384216675, 1358640717, 1333635731, 1309185222, 1285273298, 1261884644, 1239004499, 1216618632, 1194713319, 1173275322, 1152291868, 1131750631, 1111639712, 1091947620, 1072663261, 1053775914, 1035275222, 1017151175, 999394094, 981994622, 964943707, 948232593, 931852807, 915796147, 900054674, 884620699, 869486776, 854645689, 840090447, 825814274, 811810600, 798073054, 784595458, 771371818, 758396316, 745663306, 733167308, 720903000, 708865213, 697048926, 685449260, 674061473, 662880957, 651903230, 641123935, 630538832, 620143798, 609934821, 599907995, 590059517, 580385688, 570882901, 561547645, 552376501, 543366135]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 790).prefactor = (1180399607105649/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 790).cutoff/(generalMeanRows 790).c)).2 =
    (35837852186353/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 790).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 790).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 790).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 790

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 790).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 790).criticalRate j.val*(generalMeanRows 790).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 790).c*(generalMeanRows 790).criticalPoint j.val)).2-
      (generalMeanRows 790).J/2-(generalMeanRows 790).error (generalMeanGrid j.val)+
      (generalMeanRows 790).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 790).c)).2-
      (generalMeanRows 790).J/2-(generalMeanRows 790).error 4 := by
  have he : (generalMeanRows 790).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 790) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 790)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0790

/-! Kernel-checked entropy margins for general spectral rectangle 791. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0791
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6058784063, 5876011554, 5700855607, 5532900388, 5371758897, 5217070429, 5068498314, 4925727910, 4788464792, 4656433137, 4529374260, 4407045307, 4289218055, 4175677835, 4066222551, 3960661781, 3858815964, 3760515648, 3665600810, 3573920224, 3485330882, 3399697467, 3316891856, 3236792669, 3159284849, 3084259276, 3011612402, 2941245924, 2873066464, 2806985287, 2742918031, 2680784452, 2620508193, 2562016566, 2505240344, 2450113573, 2396573391, 2344559862, 2294015816, 2244886702, 2197120452, 2150667348, 2105479897, 2061512724, 2018722453, 1977067615, 1936508541, 1897007283, 1858527517, 1821034470, 1784494841, 1748876728, 1714149561, 1680284038, 1647252062, 1615026685, 1583582055, 1552893360, 1522936782, 1493689452, 1465129401, 1437235524, 1409987536, 1383365938, 1357351978, 1331927621, 1307075513, 1282778953, 1259021863, 1235788761, 1213064735, 1190835418, 1169086962, 1147806019, 1126979719, 1106595647, 1086641825, 1067106696, 1047979101, 1029248267, 1010903790, 992935618, 975334037, 958089658, 941193405, 924636498, 908410447, 892507033, 876918306, 861636567, 846654362, 831964470, 817559896, 803433862, 789579797, 775991332, 762662288, 749586674, 736758676, 724172650, 711823121, 699704771, 687812436, 676141098, 664685884, 653442058, 642405014, 631570278, 620933495, 610490432, 600236968, 590169095, 580282912, 570574620, 561040521, 551677014, 542480589, 533447828, 524575400, 515860059, 507298639]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 791).prefactor = (2305093530094121/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 791).cutoff/(generalMeanRows 791).c)).2 =
    (92987649852269/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 791).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 791).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 791).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 791

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 791).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 791).criticalRate j.val*(generalMeanRows 791).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 791).c*(generalMeanRows 791).criticalPoint j.val)).2-
      (generalMeanRows 791).J/2-(generalMeanRows 791).error (generalMeanGrid j.val)+
      (generalMeanRows 791).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 791).c)).2-
      (generalMeanRows 791).J/2-(generalMeanRows 791).error 4 := by
  have he : (generalMeanRows 791).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 791) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 791)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0791

/-! Kernel-checked entropy margins for general spectral rectangle 792. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0792
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5782129087, 5601434284, 5428355760, 5262476339, 5103407792, 4950788295, 4804280166, 4663567843, 4528356075, 4398368300, 4273345176, 4153043262, 4037233821, 3925701731, 3818244502, 3714671376, 3614802498, 3518468174, 3425508177, 3335771113, 3249113844, 3165400948, 3084504229, 3006302255, 2930679943, 2857528163, 2786743377, 2718227304, 2651886605, 2587632595, 2525380969, 2465051552, 2406568061, 2349857890, 2294851898, 2241484220, 2189692089, 2139415661, 2090597865, 2043184248, 1997122838, 1952364014, 1908860384, 1866566665, 1825439577, 1785437742, 1746521583, 1708653240, 1671796474, 1635916597, 1600980387, 1566956019, 1533813000, 1501522097, 1470055284, 1439385679, 1409487491, 1380335969, 1351907352, 1324178824, 1297128469, 1270735229, 1244978865, 1219839921, 1195299686, 1171340162, 1147944032, 1125094627, 1102775901, 1080972401, 1059669242, 1038852081, 1018507095, 998620957, 979180817, 960174279, 941589382, 923414584, 905638742, 888251096, 871241255, 854599178, 838315163, 822379830, 806784112, 791519239, 776576727, 761948369, 747626219, 733602586, 719870023, 706421316, 693249478, 680347735, 667709525, 655328484, 643198442, 631313413, 619667590, 608255339, 597071190, 586109835, 575366117, 564835029, 554511706, 544391422, 534469581, 524741720, 515203496, 505850686, 496679184, 487684994, 478864228, 470213103, 461727935, 453405137, 445241218, 437232776, 429376498, 421669155, 414107602]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 792).prefactor = (925637711900697/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 792).cutoff/(generalMeanRows 792).c)).2 =
    (180899113972529/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 792).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 792).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 792).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 792

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 792).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 792).criticalRate j.val*(generalMeanRows 792).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 792).c*(generalMeanRows 792).criticalPoint j.val)).2-
      (generalMeanRows 792).J/2-(generalMeanRows 792).error (generalMeanGrid j.val)+
      (generalMeanRows 792).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 792).c)).2-
      (generalMeanRows 792).J/2-(generalMeanRows 792).error 4 := by
  have he : (generalMeanRows 792).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 792) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 792)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0792

/-! Kernel-checked entropy margins for general spectral rectangle 793. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0793
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5339465281, 5162231145, 4992613887, 4830195218, 4674585844, 4525422934, 4382367853, 4245104140, 4113335701, 3986785180, 3865192490, 3748313496, 3635918808, 3527792697, 3423732103, 3323545735, 3227053243, 3134084467, 3044478747, 2958084281, 2874757552, 2794362781, 2716771438, 2641861779, 2569518425, 2499631969, 2432098612, 2366819827, 2303702043, 2242656353, 2183598245, 2126447346, 2071127185, 2017564977, 1965691410, 1915440458, 1866749196, 1819557634, 1773808557, 1729447375, 1686421986, 1644682643, 1604181831, 1564874152, 1526716213, 1489666529, 1453685418, 1418734919, 1384778698, 1351781971, 1319711430, 1288535162, 1258222590, 1228744403, 1200072498, 1172179918, 1145040804, 1118630337, 1092924692, 1067900991, 1043537260, 1019812387, 996706080, 974198835, 952271893, 930907215, 910087442, 889795870, 870016418, 850733602, 831932508, 813598770, 795718542, 778278479, 761265713, 744667835, 728472877, 712669287, 697245919, 682192012, 667497176, 653151375, 639144915, 625468427, 612112856, 599069450, 586329743, 573885550, 561728948, 549852276, 538248116, 526909286, 515828834, 505000026, 494416339, 484071452, 473959241, 464073767, 454409275, 444960183, 435721076, 426686702, 417851966, 409211921, 400761767, 392496842, 384412622, 376504710, 368768837, 361200853, 353796729, 346552546, 339464495, 332528874, 325742082, 319100617, 312601073, 306240136, 300014581, 293921271, 287957150]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 793).prefactor = (4637799923163123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 793).cutoff/(generalMeanRows 793).c)).2 =
    (67586149307683/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 793).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 793).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 793).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 793

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 793).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 793).criticalRate j.val*(generalMeanRows 793).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 793).c*(generalMeanRows 793).criticalPoint j.val)).2-
      (generalMeanRows 793).J/2-(generalMeanRows 793).error (generalMeanGrid j.val)+
      (generalMeanRows 793).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 793).c)).2-
      (generalMeanRows 793).J/2-(generalMeanRows 793).error 4 := by
  have he : (generalMeanRows 793).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 793) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 793)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0793

/-! Kernel-checked entropy margins for general spectral rectangle 794. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0794
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5309255077, 5140608035, 4979196680, 4824617367, 4676494718, 4534479148, 4398244663, 4267486885, 4141921291, 4021281616, 3905318425, 3793797816, 3686500249, 3583219476, 3483761575, 3387944064, 3295595094, 3206552711, 3120664174, 3037785340, 2957780085, 2880519779, 2805882802, 2733754093, 2664024734, 2596591568, 2531356839, 2468227867, 2407116735, 2347940006, 2290618460, 2235076840, 2181243625, 2129050817, 2078433733, 2029330824, 1981683494, 1935435937, 1890534985, 1846929958, 1804572535, 1763416621, 1723418232, 1684535381, 1646727970, 1609957695, 1574187951, 1539383742, 1505511603, 1472539517, 1440436843, 1409174250, 1378723646, 1349058120, 1320151884, 1291980216, 1264519406, 1237746714, 1211640315, 1186179261, 1161343437, 1137113522, 1113470951, 1090397880, 1067877153, 1045892270, 1024427358, 1003467139, 982996907, 963002501, 943470278, 924387095, 905740282, 887517624, 869707341, 852298067, 835278836, 818639061, 802368520, 786457339, 770895982, 755675228, 740786168, 726220185, 711968946, 698024388, 684378707, 671024352, 657954008, 645160592, 632637244, 620377313, 608374354, 596622120, 585114551, 573845769, 562810071, 552001925, 541415957, 531046951, 520889844, 510939715, 501191783, 491641403, 482284060, 473115364, 464131047, 455326955, 446699051, 438243404, 429956189, 421833685, 413872265, 406068400, 398418654, 390919677, 383568207, 376361066, 369295153, 362367450, 355575012]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 794).prefactor = (4497028991981241/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 794).cutoff/(generalMeanRows 794).c)).2 =
    (38068427937783/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 794).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 794).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 794).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 794

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 794).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 794).criticalRate j.val*(generalMeanRows 794).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 794).c*(generalMeanRows 794).criticalPoint j.val)).2-
      (generalMeanRows 794).J/2-(generalMeanRows 794).error (generalMeanGrid j.val)+
      (generalMeanRows 794).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 794).c)).2-
      (generalMeanRows 794).J/2-(generalMeanRows 794).error 4 := by
  have he : (generalMeanRows 794).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 794) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 794)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0794

/-! Kernel-checked entropy margins for general spectral rectangle 795. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0795
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5010032690, 4838371678, 4674244776, 4517232592, 4366944968, 4223018425, 4085113889, 3952914657, 3826124568, 3704466368, 3587680225, 3475522395, 3367764007, 3264189968, 3164597954, 3068797505, 2976609183, 2887863816, 2802401791, 2720072417, 2640733329, 2564249947, 2490494970, 2419347916, 2350694691, 2284427188, 2220442926, 2158644701, 2098940272, 2041242067, 1985466902, 1931535732, 1879373405, 1828908446, 1780072842, 1732801852, 1687033823, 1642710019, 1599774459, 1558173774, 1517857057, 1478775740, 1440883464, 1404135963, 1368490958, 1333908050, 1300348627, 1267775768, 1236154159, 1205450015, 1175630996, 1146666142, 1118525803, 1091181571, 1064606224, 1038773665, 1013658870, 989237836, 965487530, 942385848, 919911566, 898044303, 876764480, 856053283, 835892626, 816265124, 797154053, 778543327, 760417465, 742761567, 725561286, 708802807, 692472819, 676558496, 661047477, 645927844, 631188105, 616817172, 602804350, 589139315, 575812103, 562813092, 550132988, 537762814, 525693895, 513917847, 502426566, 491212212, 480267207, 469584218, 459156147, 448976128, 439037513, 429333865, 419858949, 410606727, 401571348, 392747142, 384128613, 375710433, 367487436, 359454611, 351607099, 343940183, 336449287, 329129970, 321977920, 314988951, 308158997, 301484110, 294960455, 288584305, 282352037, 276260133, 270305170, 264483823, 258792856, 253229125, 247789568, 242471211, 237271156]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 795).prefactor = (4627804855097353/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 795).cutoff/(generalMeanRows 795).c)).2 =
    (68421473219313/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 795).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 795).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 795).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 795

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 795).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 795).criticalRate j.val*(generalMeanRows 795).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 795).c*(generalMeanRows 795).criticalPoint j.val)).2-
      (generalMeanRows 795).J/2-(generalMeanRows 795).error (generalMeanGrid j.val)+
      (generalMeanRows 795).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 795).c)).2-
      (generalMeanRows 795).J/2-(generalMeanRows 795).error 4 := by
  have he : (generalMeanRows 795).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 795) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 795)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0795

/-! Kernel-checked entropy margins for general spectral rectangle 796. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0796
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5138802373, 4970648088, 4809812061, 4655883339, 4508479823, 4367245745, 4231849419, 4101981229, 3977351828, 3857690512, 3742743759, 3632273904, 3526057940, 3423886430, 3325562514, 3230901006, 3139727568, 3051877954, 2967197315, 2885539565, 2806766795, 2730748733, 2657362246, 2586490883, 2518024449, 2451858611, 2387894535, 2326038547, 2266201820, 2208300080, 2152253338, 2097985633, 2045424797, 1994502238, 1945152732, 1897314229, 1850927678, 1805936855, 1762288209, 1719930713, 1678815724, 1638896856, 1600129860, 1562472502, 1525884466, 1490327245, 1455764050, 1422159719, 1389480634, 1357694640, 1326770973, 1296680188, 1267394091, 1238885681, 1211129084, 1184099505, 1157773169, 1132127275, 1107139945, 1082790186, 1059057841, 1035923551, 1013368721, 991375480, 969926648, 949005707, 928596766, 908684535, 889254298, 870291885, 851783651, 833716447, 816077605, 798854911, 782036587, 765611274, 749568011, 733896220, 718585690, 703626557, 689009295, 674724701, 660763879, 647118227, 633779429, 620739440, 607990477, 595525006, 583335735, 571415601, 559757767, 548355605, 537202696, 526292815, 515619928, 505178185, 494961909, 484965595, 475183899, 465611633, 456243763, 447075399, 438101792, 429318326, 420720520, 412304017, 404064579, 395998091, 388100545, 380368049, 372796811, 365383146, 358123465, 351014275, 344052176, 337233857, 330556095, 324015749, 317609758, 311335144, 305189001]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 796).prefactor = (1138282550979981/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 796).cutoff/(generalMeanRows 796).c)).2 =
    (188343849846671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 796).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 796).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 796).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 796

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 796).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 796).criticalRate j.val*(generalMeanRows 796).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 796).c*(generalMeanRows 796).criticalPoint j.val)).2-
      (generalMeanRows 796).J/2-(generalMeanRows 796).error (generalMeanGrid j.val)+
      (generalMeanRows 796).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 796).c)).2-
      (generalMeanRows 796).J/2-(generalMeanRows 796).error 4 := by
  have he : (generalMeanRows 796).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 796) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 796)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0796

/-! Kernel-checked entropy margins for general spectral rectangle 797. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0797
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5216557005, 5046082286, 4882972916, 4726818778, 4577238422, 4433876555, 4296401808, 4164504739, 4037896040, 3916304927, 3799477688, 3687176370, 3579177591, 3475271455, 3375260575, 3278959175, 3186192270, 3096794919, 3010611535, 2927495259, 2847307374, 2769916778, 2695199482, 2623038165, 2553321744, 2485944993, 2420808172, 2357816700, 2296880841, 2237915413, 2180839519, 2125576297, 2072052685, 2020199202, 1969949747, 1921241403, 1874014264, 1828211261, 1783778015, 1740662682, 1698815819, 1658190255, 1618740968, 1580424973, 1543201215, 1507030466, 1471875232, 1437699663, 1404469470, 1372151844, 1340715383, 1310130020, 1280366958, 1251398606, 1223198521, 1195741350, 1169002779, 1142959482, 1117589073, 1092870063, 1068781816, 1045304511, 1022419101, 1000107279, 978351442, 957134662, 936440653, 916253742, 896558840, 877341420, 858587488, 840283561, 822416646, 804974214, 787944187, 771314911, 755075144, 739214034, 723721106, 708586244, 693799676, 679351960, 665233973, 651436893, 637952192, 624771619, 611887192, 599291189, 586976133, 574934785, 563160136, 551645396, 540383984, 529369526, 518595839, 508056932, 497746993, 487660383, 477791634, 468135436, 458686637, 449440234, 440391370, 431535326, 422867518, 414383493, 406078921, 397949596, 389991425, 382200432, 374572747, 367104606, 359792346, 352632406, 345621315, 338755697, 332032266, 325447819, 318999240, 312683491, 306497612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 797).prefactor = (1141191224772489/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 797).cutoff/(generalMeanRows 797).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 797).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 797).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 797).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 797

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 797).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 797).criticalRate j.val*(generalMeanRows 797).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 797).c*(generalMeanRows 797).criticalPoint j.val)).2-
      (generalMeanRows 797).J/2-(generalMeanRows 797).error (generalMeanGrid j.val)+
      (generalMeanRows 797).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 797).c)).2-
      (generalMeanRows 797).J/2-(generalMeanRows 797).error 4 := by
  have he : (generalMeanRows 797).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 797) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 797)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0797

/-! Kernel-checked entropy margins for general spectral rectangle 798. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0798
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5311510894, 5145124685, 4985886874, 4833395505, 4687276915, 4547183261, 4412790315, 4283795484, 4159916047, 4040887553, 3926462393, 3816408496, 3710508152, 3608556946, 3510362783, 3415744999, 3324533554, 3236568289, 3151698243, 3069781031, 2990682271, 2914275050, 2840439443, 2769062054, 2700035607, 2633258556, 2568634731, 2506073001, 2445486971, 2386794696, 2329918409, 2274784281, 2221322182, 2169465470, 2119150791, 2070317885, 2022909414, 1976870801, 1932150066, 1888697692, 1846466483, 1805411441, 1765489645, 1726660139, 1688883828, 1652123377, 1616343124, 1581508983, 1547588373, 1514550130, 1482364442, 1451002775, 1420437813, 1390643392, 1361594444, 1333266945, 1305637860, 1278685096, 1252387457, 1226724598, 1201676987, 1177225865, 1153353207, 1130041691, 1107274663, 1085036105, 1063310609, 1042083343, 1021340031, 1001066925, 981250780, 961878831, 942938777, 924418752, 906307313, 888593419, 871266413, 854316004, 837732255, 821505566, 805626660, 790086568, 774876618, 759988422, 745413865, 731145092, 717174500, 703494727, 690098640, 676979329, 664130097, 651544452, 639216099, 627138931, 615307025, 603714631, 592356169, 581226220, 570319523, 559630965, 549155581, 538888544, 528825160, 518960869, 509291233, 499811936, 490518778, 481407675, 472474647, 463715822, 455127429, 446705796, 438447345, 430348589, 422406133, 414616664, 406976955, 399483859, 392134306, 384925302, 377853928]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 798).prefactor = (1122363451522039/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 798).cutoff/(generalMeanRows 798).c)).2 =
    (397291159227731/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 798).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 798).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 798).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 798

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 798).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 798).criticalRate j.val*(generalMeanRows 798).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 798).c*(generalMeanRows 798).criticalPoint j.val)).2-
      (generalMeanRows 798).J/2-(generalMeanRows 798).error (generalMeanGrid j.val)+
      (generalMeanRows 798).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 798).c)).2-
      (generalMeanRows 798).J/2-(generalMeanRows 798).error 4 := by
  have he : (generalMeanRows 798).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 798) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 798)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0798

/-! Kernel-checked entropy margins for general spectral rectangle 799. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0799
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5271788249, 5104109584, 4943703959, 4790160387, 4643096859, 4502157814, 4367011877, 4237349840, 4112882846, 3993340758, 3878470690, 3768035669, 3661813438, 3559595354, 3461185390, 3366399229, 3275063433, 3187014678, 3102099059, 3020171452, 2941094919, 2864740172, 2790985067, 2719714145, 2650818204, 2584193904, 2519743400, 2457374001, 2396997857, 2338531662, 2281896383, 2227017007, 2173822301, 2122244593, 2072219565, 2023686060, 1976585903, 1930863730, 1886466834, 1843345012, 1801450432, 1760737500, 1721162738, 1682684670, 1645263716, 1608862089, 1573443700, 1538974071, 1505420248, 1472750724, 1440935364, 1409945333, 1379753033, 1350332037, 1321657033, 1293703766, 1266448989, 1239870408, 1213946642, 1188657171, 1163982301, 1139903122, 1116401467, 1093459884, 1071061594, 1049190468, 1027830988, 1006968226, 986587813, 966675914, 947219206, 928204850, 909620475, 891454153, 873694383, 856330067, 839350498, 822745341, 806504615, 790618679, 775078222, 759874240, 744998032, 730441183, 716195551, 702253260, 688606686, 675248448, 662171398, 649368610, 636833375, 624559190, 612539750, 600768941, 589240831, 577949667, 566889864, 556056000, 545442812, 535045187, 524858159, 514876903, 505096727, 495513074, 486121509, 476917720, 467897515, 459056812, 450391639, 441898132, 433572527, 425411159, 417410460, 409566953, 401877249, 394338049, 386946134, 379698369, 372591696, 365623131, 358789768]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 799).prefactor = (4547424013638751/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 799).cutoff/(generalMeanRows 799).c)).2 =
    (39712300572099/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 799).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 799).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 799).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 799

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 799).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 799).criticalRate j.val*(generalMeanRows 799).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 799).c*(generalMeanRows 799).criticalPoint j.val)).2-
      (generalMeanRows 799).J/2-(generalMeanRows 799).error (generalMeanGrid j.val)+
      (generalMeanRows 799).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 799).c)).2-
      (generalMeanRows 799).J/2-(generalMeanRows 799).error 4 := by
  have he : (generalMeanRows 799).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 799) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 799)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0799

/-! Kernel-checked entropy margins for general spectral rectangle 800. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0800
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5222195850, 5053652726, 4892445044, 4738158730, 4590408877, 4448837200, 4313109758, 4182914924, 4057961556, 3937977358, 3822707398, 3711912769, 3605369373, 3502866823, 3404207434, 3309205312, 3217685514, 3129483286, 3044443359, 2962419305, 2883272943, 2806873795, 2733098582, 2661830757, 2592960078, 2526382208, 2461998347, 2399714890, 2339443108, 2281098853, 2224602286, 2169877616, 2116852866, 2065459649, 2015632958, 1967310976, 1920434892, 1874948732, 1830799200, 1787935528, 1746309340, 1705874517, 1666587079, 1628405064, 1591288424, 1555198923, 1520100039, 1485956876, 1452736078, 1420405753, 1388935391, 1358295799, 1328459032, 1299398331, 1271088062, 1243503661, 1216621584, 1190419250, 1164874999, 1139968049, 1115678447, 1091987036, 1068875413, 1046325895, 1024321485, 1002845840, 981883240, 961418559, 941437240, 921925266, 902869138, 884255851, 866072871, 848308116, 830949934, 813987085, 797408725, 781204385, 765363958, 749877683, 734736130, 719930184, 705451037, 691290171, 677439347, 663890593, 650636196, 637668688, 624980840, 612565647, 600416326, 588526301, 576889200, 565498843, 554349238, 543434572, 532749204, 522287660, 512044627, 502014945, 492193602, 482575730, 473156599, 463931612, 454896300, 446046319, 437377443, 428885563, 420566680, 412416904, 404432447, 396609624, 388944845, 381434616, 374075533, 366864279, 359797623, 352872418, 346085593, 339434158, 332915196]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 800).prefactor = (2289901035184727/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 800).cutoff/(generalMeanRows 800).c)).2 =
    (389632333991831/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 800).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 800).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 800).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 800

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 800).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 800).criticalRate j.val*(generalMeanRows 800).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 800).c*(generalMeanRows 800).criticalPoint j.val)).2-
      (generalMeanRows 800).J/2-(generalMeanRows 800).error (generalMeanGrid j.val)+
      (generalMeanRows 800).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 800).c)).2-
      (generalMeanRows 800).J/2-(generalMeanRows 800).error 4 := by
  have he : (generalMeanRows 800).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 800) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 800)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0800

/-! Kernel-checked entropy margins for general spectral rectangle 801. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0801
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5176026571, 5006654218, 4844653135, 4689609392, 4541138122, 4398880980, 4262503876, 4131694954, 4006162768, 3885634656, 3769855257, 3658585186, 3551599821, 3448688206, 3349652056, 3254304844, 3162470969, 3073984994, 2988690949, 2906441691, 2827098311, 2750529593, 2676611513, 2605226776, 2536264388, 2469619261, 2405191845, 2342887788, 2282617618, 2224296453, 2167843722, 2113182915, 2060241342, 2008949913, 1959242931, 1911057898, 1864335334, 1819018609, 1775053784, 1732389460, 1690976645, 1650768615, 1611720800, 1573790662, 1536937591, 1501122803, 1466309240, 1432461488, 1399545684, 1367529440, 1336381770, 1306073015, 1276574777, 1247859858, 1219902200, 1192676825, 1166159788, 1140328121, 1115159790, 1090633647, 1066729390, 1043427522, 1020709310, 998556755, 976952554, 955880066, 935323288, 915266818, 895695833, 876596062, 857953758, 839755681, 821989067, 804641616, 787701464, 771157170, 754997694, 739212381, 723790944, 708723451, 694000306, 679612238, 665550287, 651805789, 638370369, 625235921, 612394608, 599838840, 587561273, 575554793, 563812512, 552327756, 541094058, 530105148, 519354950, 508837569, 498547290, 488478565, 478626012, 468984407, 459548679, 450313901, 441275291, 432428201, 423768115, 415290644, 406991522, 398866602, 390911848, 383123340, 375497258, 368029890, 360717621, 353556934, 346544404, 339676695, 332950561, 326362837, 319910444, 313590378, 307399713]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 801).prefactor = (4586111938975013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 801).cutoff/(generalMeanRows 801).c)).2 =
    (188343849846671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 801).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 801).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 801).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 801

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 801).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 801).criticalRate j.val*(generalMeanRows 801).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 801).c*(generalMeanRows 801).criticalPoint j.val)).2-
      (generalMeanRows 801).J/2-(generalMeanRows 801).error (generalMeanGrid j.val)+
      (generalMeanRows 801).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 801).c)).2-
      (generalMeanRows 801).J/2-(generalMeanRows 801).error 4 := by
  have he : (generalMeanRows 801).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 801) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 801)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0801

/-! Kernel-checked entropy margins for general spectral rectangle 802. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0802
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5046638722, 4876880482, 4714566076, 4559278109, 4410628436, 4268255604, 4131822578, 4001014698, 3875537856, 3755116851, 3639493904, 3528427322, 3421690277, 3319069706, 3220365308, 3125388625, 3033962206, 2945918842, 2861100863, 2779359493, 2700554257, 2624552434, 2551228553, 2480463931, 2412146236, 2346169094, 2282431720, 2220838570, 2161299027, 2103727106, 2048041174, 1994163698, 1942021003, 1891543051, 1842663230, 1795318162, 1749447519, 1704993855, 1661902441, 1620121123, 1579600175, 1540292174, 1502151868, 1465136069, 1429203538, 1394314884, 1360432468, 1327520315, 1295544021, 1264470680, 1234268805, 1204908257, 1176360175, 1148596917, 1121591996, 1095320026, 1069756665, 1044878568, 1020663336, 997089473, 974136341, 951784122, 930013776, 908807009, 888146233, 868014540, 848395665, 829273960, 810634365, 792462384, 774744054, 757465927, 740615046, 724178923, 708145515, 692503214, 677240817, 662347517, 647812884, 633626847, 619779682, 606261995, 593064710, 580179055, 567596551, 555308999, 543308469, 531587288, 520138033, 508953518, 498026786, 487351101, 476919937, 466726972, 456766081, 447031326, 437516950, 428217371, 419127175, 410241110, 401554080, 393061139, 384757486, 376638459, 368699533, 360936309, 353344519, 345920011, 338658753, 331556824, 324610414, 317815816, 311169429, 304667746, 298307357, 292084945, 285997281, 280041222, 274213711, 268511767, 262932493]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 802).prefactor = (1154833146364983/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 802).cutoff/(generalMeanRows 802).c)).2 =
    (7239631046073/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 802).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 802).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 802).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 802

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 802).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 802).criticalRate j.val*(generalMeanRows 802).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 802).c*(generalMeanRows 802).criticalPoint j.val)).2-
      (generalMeanRows 802).J/2-(generalMeanRows 802).error (generalMeanGrid j.val)+
      (generalMeanRows 802).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 802).c)).2-
      (generalMeanRows 802).J/2-(generalMeanRows 802).error 4 := by
  have he : (generalMeanRows 802).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 802) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 802)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0802

/-! Kernel-checked entropy margins for general spectral rectangle 803. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0803
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5089423106, 4920447202, 4758879063, 4604301262, 4456325723, 4314591152, 4178760753, 4048520182, 3923575713, 3803652587, 3688493521, 3577857361, 3471517865, 3369262590, 3270891885, 3176217971, 3085064098, 2997263777, 2912660074, 2831104959, 2752458715, 2676589385, 2603372267, 2532689444, 2464429357, 2398486400, 2334760550, 2273157022, 2213585953, 2155962102, 2100204572, 2046236556, 1993985095, 1943380856, 1894357920, 1846853588, 1800808199, 1756164961, 1712869785, 1670871143, 1630119921, 1590569292, 1552174588, 1514893190, 1478684411, 1443509400, 1409331044, 1376113874, 1343823986, 1312428954, 1281897757, 1252200710, 1223309392, 1195196587, 1167836221, 1141203305, 1115273885, 1090024989, 1065434580, 1041481509, 1018145476, 995406988, 973247318, 951648473, 930593160, 910064748, 890047243, 870525258, 851483983, 832909161, 814787060, 797104455, 779848601, 763007212, 746568446, 730520876, 714853484, 699555633, 684617057, 670027842, 655778414, 641859523, 628262229, 614977892, 601998155, 589314938, 576920422, 564807043, 552967478, 541394637, 530081655, 519021880, 508208869, 497636377, 487298350, 477188919, 467302391, 457633244, 448176121, 438925822, 429877299, 421025654, 412366126, 403894094, 395605067, 387494683, 379558700, 371792998, 364193566, 356756510, 349478036, 342354459, 335382191, 328557739, 321877705, 315338782, 308937749, 302671469, 296536887, 290531028, 284650994]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 803).prefactor = (2306205330848063/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 803).cutoff/(generalMeanRows 803).c)).2 =
    (374817248206691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 803).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 803).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 803).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 803

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 803).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 803).criticalRate j.val*(generalMeanRows 803).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 803).c*(generalMeanRows 803).criticalPoint j.val)).2-
      (generalMeanRows 803).J/2-(generalMeanRows 803).error (generalMeanGrid j.val)+
      (generalMeanRows 803).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 803).c)).2-
      (generalMeanRows 803).J/2-(generalMeanRows 803).error 4 := by
  have he : (generalMeanRows 803).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 803) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 803)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0803

/-! Kernel-checked entropy margins for general spectral rectangle 804. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0804
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4961652247, 4792374589, 4630575772, 4475834896, 4327760596, 4185988466, 4050178754, 3920014310, 3795198739, 3675454739, 3560522605, 3450158872, 3344135092, 3242236713, 3144262067, 3050021446, 2959336252, 2872038226, 2787968736, 2706978126, 2628925117, 2553676251, 2481105389, 2411093230, 2343526888, 2278299478, 2215309749, 2154461739, 2095664448, 2038831542, 1983881075, 1930735231, 1879320076, 1829565343, 1781404212, 1734773118, 1689611568, 1645861965, 1603469451, 1562381753, 1522549044, 1483923809, 1446460720, 1410116520, 1374849911, 1340621456, 1307393474, 1275129955, 1243796470, 1213360093, 1183789322, 1155054008, 1127125286, 1099975514, 1073578207, 1047907987, 1022940522, 998652479, 975021476, 952026034, 929645536, 907860186, 886650967, 865999610, 845888556, 826300923, 807220476, 788631599, 770519261, 752868997, 735666879, 718899492, 702553913, 686617686, 671078807, 655925699, 641147198, 626732532, 612671306, 598953487, 585569386, 572509647, 559765230, 547327401, 535187717, 523338017, 511770408, 500477254, 489451170, 478685006, 468171844, 457904984, 447877938, 438084422, 428518347, 419173812, 410045099, 401126662, 392413124, 383899271, 375580042, 367450530, 359505971, 351741738, 344153344, 336736428, 329486756, 322400214, 315472806, 308700649, 302079967, 295607091, 289278454, 283090587, 277040116, 271123759, 265338322, 259680700, 254147869, 248736887, 243444887]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 804).prefactor = (4645251429045243/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 804).cutoff/(generalMeanRows 804).c)).2 =
    (180109224392769/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 804).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 804).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 804).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 804

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 804).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 804).criticalRate j.val*(generalMeanRows 804).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 804).c*(generalMeanRows 804).criticalPoint j.val)).2-
      (generalMeanRows 804).J/2-(generalMeanRows 804).error (generalMeanGrid j.val)+
      (generalMeanRows 804).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 804).c)).2-
      (generalMeanRows 804).J/2-(generalMeanRows 804).error 4 := by
  have he : (generalMeanRows 804).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 804) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 804)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0804

/-! Kernel-checked entropy margins for general spectral rectangle 805. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0805
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5001798185, 4831280539, 4668269564, 4512344571, 4363114325, 4220214467, 4083305229, 3952069373, 3826210362, 3705450696, 3589530428, 3478205804, 3371248051, 3268442260, 3169586373, 3074490267, 2982974908, 2894871581, 2810021180, 2728273564, 2649486955, 2573527392, 2500268218, 2429589620, 2361378186, 2295526510, 2231932821, 2170500633, 2111138427, 2053759355, 1998280960, 1944624917, 1892716796, 1842485834, 1793864726, 1746789428, 1701198975, 1657035311, 1614243122, 1572769693, 1532564762, 1493580387, 1455770825, 1419092412, 1383503456, 1348964130, 1315436377, 1282883822, 1251271676, 1220566666, 1190736950, 1161752052, 1133582788, 1106201202, 1079580512, 1053695044, 1028520184, 1004032324, 980208815, 957027920, 934468771, 912511330, 891136347, 870325325, 850060485, 830324733, 811101630, 792375359, 774130699, 756352999, 739028153, 722142573, 705683167, 689637320, 673992872, 658738096, 643861682, 629352720, 615200680, 601395398, 587927061, 574786191, 561963633, 549450539, 537238361, 525318831, 513683955, 502326004, 491237497, 480411196, 469840095, 459517412, 449436579, 439591235, 429975216, 420582551, 411407452, 402444307, 393687677, 385132286, 376773014, 368604897, 360623116, 352822994, 345199991, 337749699, 330467837, 323350246, 316392888, 309591836, 302943276, 296443502, 290088908, 283875989, 277801339, 271861642, 266053674, 260374298, 254820462, 249389194, 244077604]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 805).prefactor = (290799617124329/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 805).cutoff/(generalMeanRows 805).c)).2 =
    (44338599121821/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 805).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 805).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 805).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 805

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 805).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 805).criticalRate j.val*(generalMeanRows 805).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 805).c*(generalMeanRows 805).criticalPoint j.val)).2-
      (generalMeanRows 805).J/2-(generalMeanRows 805).error (generalMeanGrid j.val)+
      (generalMeanRows 805).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 805).c)).2-
      (generalMeanRows 805).J/2-(generalMeanRows 805).error 4 := by
  have he : (generalMeanRows 805).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 805) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 805)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0805

/-! Kernel-checked entropy margins for general spectral rectangle 806. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0806
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5309823395, 5143425988, 4984227406, 4831819365, 4685822457, 4545883628, 4411673924, 4282886477, 4159234694, 4040450632, 3926283525, 3816498462, 3710875180, 3609206969, 3511299682, 3416970820, 3326048711, 3238371742, 3153787670, 3072152980, 2993332295, 2917197841, 2843628938, 2772511550, 2703737851, 2637205833, 2572818942, 2510485736, 2450119572, 2391638317, 2334964066, 2280022902, 2226744647, 2175062651, 2124913583, 2076237240, 2028976365, 1983076485, 1938485747, 1895154778, 1853036541, 1812086212, 1772261053, 1733520303, 1695825069, 1659138226, 1623424324, 1588649498, 1554781385, 1521789045, 1489642890, 1458314609, 1427777109, 1398004449, 1368971781, 1340655298, 1313032180, 1286080548, 1259779413, 1234108635, 1209048883, 1184581594, 1160688936, 1137353773, 1114559634, 1092290680, 1070531675, 1049267956, 1028485411, 1008170449, 988309977, 968891382, 949902503, 931331616, 913167410, 895398973, 878015772, 861007637, 844364748, 828077613, 812137062, 796534230, 781260542, 766307704, 751667693, 737332738, 723295321, 709548157, 696084189, 682896580, 669978701, 657324126, 644926622, 632780141, 620878816, 609216952, 597789019, 586589647, 575613619, 564855868, 554311468, 543975630, 533843698, 523911145, 514173566, 504626676, 495266303, 486088389, 477088979, 468264225, 459610378, 451123785, 442800888, 434638217, 426632392, 418780116, 411078175, 403523434, 396112836, 388843397, 381712205]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 806).prefactor = (283784994163571/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 806).cutoff/(generalMeanRows 806).c)).2 =
    (204110114879961/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 806).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 806).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 806).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 806

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 806).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 806).criticalRate j.val*(generalMeanRows 806).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 806).c*(generalMeanRows 806).criticalPoint j.val)).2-
      (generalMeanRows 806).J/2-(generalMeanRows 806).error (generalMeanGrid j.val)+
      (generalMeanRows 806).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 806).c)).2-
      (generalMeanRows 806).J/2-(generalMeanRows 806).error 4 := by
  have he : (generalMeanRows 806).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 806) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 806)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0806

/-! Kernel-checked entropy margins for general spectral rectangle 807. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0807
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5214707074, 5046545165, 4885657182, 4731634983, 4584099100, 4442696229, 4307097001, 4176993973, 4052099844, 3932145836, 3816880238, 3706067097, 3599485017, 3496926083, 3398194875, 3303107563, 3211491095, 3123182438, 3038027895, 2955882467, 2876609274, 2800079021, 2726169500, 2654765134, 2585756559, 2519040228, 2454518054, 2392097069, 2331689118, 2273210562, 2216582015, 2161728088, 2108577155, 2057061139, 2007115301, 1958678056, 1911690790, 1866097694, 1821845611, 1778883886, 1737164230, 1696640592, 1657269037, 1619007634, 1581816348, 1545656941, 1510492878, 1476289235, 1443012621, 1410631095, 1379114093, 1348432360, 1318557882, 1289463825, 1261124475, 1233515183, 1206612316, 1180393202, 1154836088, 1129920093, 1105625169, 1081932056, 1058822253, 1036277974, 1014282122, 992818250, 971870538, 951423758, 931463252, 911974905, 892945117, 874360785, 856209280, 838478422, 821156468, 804232084, 787694334, 771532661, 755736871, 740297116, 725203881, 710447973, 696020499, 681912865, 668116753, 654624120, 641427177, 628518387, 615890451, 603536296, 591449075, 579622147, 568049080, 556723632, 545639755, 534791578, 524173407, 513779714, 503605135, 493644459, 483892627, 474344725, 464995978, 455841745, 446877517, 438098906, 429501650, 421081602, 412834725, 404757095, 396844891, 389094395, 381501987, 374064141, 366777425, 359638495, 352644093, 345791046, 339076260, 332496720, 326049487]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 807).prefactor = (569314997349073/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 807).cutoff/(generalMeanRows 807).c)).2 =
    (382476073442591/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 807).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 807).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 807).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 807

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 807).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 807).criticalRate j.val*(generalMeanRows 807).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 807).c*(generalMeanRows 807).criticalPoint j.val)).2-
      (generalMeanRows 807).J/2-(generalMeanRows 807).error (generalMeanGrid j.val)+
      (generalMeanRows 807).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 807).c)).2-
      (generalMeanRows 807).J/2-(generalMeanRows 807).error 4 := by
  have he : (generalMeanRows 807).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 807) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 807)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0807

/-! Kernel-checked entropy margins for general spectral rectangle 808. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0808
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5261356609, 5094055150, 4933990559, 4780754632, 4633967937, 4493277303, 4358353570, 4228889585, 4104598402, 3985211659, 3870478117, 3760162340, 3654043496, 3551914268, 3453579867, 3358857126, 3267573674, 3179567184, 3094684679, 3012781895, 2933722697, 2857378543, 2783627983, 2712356202, 2643454598, 2576820387, 2512356240, 2449969945, 2389574095, 2331085797, 2274426400, 2219521240, 2166299412, 2114693542, 2064639591, 2016076655, 1968946793, 1923194858, 1878768338, 1835617212, 1793693811, 1752952690, 1713350508, 1674845912, 1637399432, 1600973381, 1565531759, 1531040168, 1497465725, 1464776983, 1432943860, 1401937570, 1371730553, 1342296415, 1313609871, 1285646689, 1258383636, 1231798433, 1205869703, 1180576932, 1155900424, 1131821265, 1108321282, 1085383012, 1062989665, 1041125095, 1019773767, 998920735, 978551607, 958652527, 939210145, 920211599, 901644489, 883496860, 865757181, 848414326, 831457556, 814876505, 798661160, 782801849, 767289227, 752114260, 737268211, 722742633, 708529352, 694620458, 681008294, 667685446, 654644731, 641879194, 629382092, 617146890, 605167250, 593437027, 581950258, 570701159, 559684114, 548893672, 538324539, 527971574, 517829782, 507894308, 498160434, 488623574, 479279268, 470123178, 461151084, 452358879, 443742568, 435298261, 427022171, 418910610, 410959986, 403166801, 395527645, 388039196, 380698215, 373501548, 366446115, 359528916, 352747023]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 808).prefactor = (4547483864124269/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 808).cutoff/(generalMeanRows 808).c)).2 =
    (19765289275389/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 808).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 808).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 808).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 808

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 808).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 808).criticalRate j.val*(generalMeanRows 808).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 808).c*(generalMeanRows 808).criticalPoint j.val)).2-
      (generalMeanRows 808).J/2-(generalMeanRows 808).error (generalMeanGrid j.val)+
      (generalMeanRows 808).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 808).c)).2-
      (generalMeanRows 808).J/2-(generalMeanRows 808).error 4 := by
  have he : (generalMeanRows 808).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 808) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 808)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0808

/-! Kernel-checked entropy margins for general spectral rectangle 809. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0809
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5212378796, 5044224040, 4883368348, 4729400432, 4581937966, 4440625055, 4305129974, 4175143154, 4050375362, 3930556078, 3815432018, 3704765810, 3598334782, 3495929874, 3397354635, 3302424322, 3210965060, 3122813091, 3037814071, 2955822435, 2876700802, 2800319442, 2726555768, 2655293878, 2586424129, 2519842740, 2455451428, 2393157066, 2332871370, 2274510606, 2217995312, 2163250054, 2110203179, 2058786600, 2008935589, 1960588584, 1913687011, 1868175109, 1823999782, 1781110444, 1739458884, 1698999135, 1659687352, 1621481699, 1584342241, 1548230842, 1513111072, 1478948116, 1445708690, 1413360965, 1381874488, 1351220113, 1321369937, 1292297237, 1263976407, 1236382909, 1209493215, 1183284759, 1157735891, 1132825834, 1108534638, 1084843144, 1061732943, 1039186346, 1017186346, 995716585, 974761330, 954305437, 934334331, 914833974, 895790846, 877191917, 859024630, 841276876, 823936978, 806993668, 790436073, 774253695, 758436400, 742974395, 727858221, 713078733, 698627092, 684494748, 670673432, 657155143, 643932135, 630996911, 618342208, 605960995, 593846456, 581991985, 570391181, 559037835, 547925925, 537049609, 526403218, 515981251, 505778365, 495789374, 486009240, 476433067, 467056101, 457873718, 448881425, 440074853, 431449752, 423001990, 414727544, 406622501, 398683053, 390905493, 383286209, 375821687, 368508502, 361343319, 354322888, 347444041, 340703692, 334098831, 327626525]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 809).prefactor = (2289877544769717/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 809).cutoff/(generalMeanRows 809).c)).2 =
    (193962839105079/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 809).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 809).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 809).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 809

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 809).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 809).criticalRate j.val*(generalMeanRows 809).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 809).c*(generalMeanRows 809).criticalPoint j.val)).2-
      (generalMeanRows 809).J/2-(generalMeanRows 809).error (generalMeanGrid j.val)+
      (generalMeanRows 809).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 809).c)).2-
      (generalMeanRows 809).J/2-(generalMeanRows 809).error 4 := by
  have he : (generalMeanRows 809).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 809) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 809)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0809

/-! Kernel-checked entropy margins for general spectral rectangle 810. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0810
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5167582634, 4998578459, 4836911147, 4682169389, 4533970745, 4391959114, 4255802495, 4125190963, 3999834874, 3879463231, 3763822231, 3652673931, 3545795053, 3442975893, 3344019330, 3248739921, 3156963074, 3068524292, 2983268481, 2901049311, 2821728631, 2745175931, 2671267843, 2599887684, 2530925027, 2464275311, 2399839477, 2337523628, 2277238714, 2218900244, 2162428011, 2107745840, 2054781352, 2003465745, 1953733586, 1905522622, 1858773599, 1813430093, 1769438354, 1726747159, 1685307674, 1645073321, 1605999663, 1568044282, 1531166677, 1495328161, 1460491767, 1426622157, 1393685541, 1361649592, 1330483380, 1300157293, 1270642975, 1241913264, 1213942129, 1186704620, 1160176809, 1134335745, 1109159403, 1084626644, 1060717168, 1037411478, 1014690839, 992537247, 970933389, 949862615, 929308908, 909256852, 889691608, 870598886, 851964920, 833776448, 816020686, 798685309, 781758430, 765228583, 749084702, 733316105, 717912480, 702863867, 688160642, 673793507, 659753472, 646031848, 632620228, 619510482, 606694739, 594165385, 581915046, 569936580, 558223072, 546767819, 535564326, 524606297, 513887628, 503402399, 493144866, 483109457, 473290764, 463683537, 454282681, 445083244, 436080420, 427269536, 418646055, 410205565, 401943778, 393856522, 385939744, 378189499, 370601950, 363173363, 355900104, 348778636, 341805516, 334977391, 328290996, 321743150, 315330754, 309050791, 302900318]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 810).prefactor = (45874058448899/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 810).cutoff/(generalMeanRows 810).c)).2 =
    (375150033350519/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 810).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 810).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 810).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 810

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 810).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 810).criticalRate j.val*(generalMeanRows 810).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 810).c*(generalMeanRows 810).criticalPoint j.val)).2-
      (generalMeanRows 810).J/2-(generalMeanRows 810).error (generalMeanGrid j.val)+
      (generalMeanRows 810).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 810).c)).2-
      (generalMeanRows 810).J/2-(generalMeanRows 810).error 4 := by
  have he : (generalMeanRows 810).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 810) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 810)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0810

/-! Kernel-checked entropy margins for general spectral rectangle 811. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0811
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5121291165, 4951473981, 4789056672, 4633624713, 4484792645, 4342201531, 4205516693, 4074425690, 3948636496, 3827875870, 3711887878, 3600432564, 3493284739, 3390232886, 3291078163, 3195633487, 3103722711, 3015179854, 2929848409, 2847580699, 2768237287, 2691686439, 2617803613, 2546471007, 2477577125, 2411016381, 2346688738, 2284499359, 2224358300, 2166180209, 2109884053, 2055392870, 2002633523, 1951536483, 1902035622, 1854068017, 1807573774, 1762495853, 1718779914, 1676374166, 1635229230, 1595298006, 1556535553, 1518898971, 1482347296, 1446841396, 1412343875, 1378818984, 1346232538, 1314551833, 1283745571, 1253783791, 1224637802, 1196280117, 1168684397, 1141825391, 1115678886, 1090221656, 1065431412, 1041286761, 1017767161, 994852880, 972524961, 950765182, 929556026, 908880645, 888722832, 869066989, 849898104, 831201718, 812963908, 795171257, 777810836, 760870179, 744337266, 728200502, 712448699, 697071059, 682057158, 667396929, 653080648, 639098919, 625442662, 612103098, 599071738, 586340373, 573901057, 561746105, 549868074, 538259761, 526914187, 515824594, 504984434, 494387359, 484027217, 473898043, 463994053, 454309634, 444839342, 435577893, 426520158, 417661159, 408996061, 400520167, 392228915, 384117874, 376182736, 368419314, 360823537, 353391448, 346119197, 339003040, 332039336, 325224539, 318555200, 312027962, 305639556, 299386800, 293266596, 287275924, 281411845]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 811).prefactor = (4620529163055491/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 811).cutoff/(generalMeanRows 811).c)).2 =
    (1149616481317/3125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 811).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 811).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 811).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 811

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 811).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 811).criticalRate j.val*(generalMeanRows 811).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 811).c*(generalMeanRows 811).criticalPoint j.val)).2-
      (generalMeanRows 811).J/2-(generalMeanRows 811).error (generalMeanGrid j.val)+
      (generalMeanRows 811).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 811).c)).2-
      (generalMeanRows 811).J/2-(generalMeanRows 811).error 4 := by
  have he : (generalMeanRows 811).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 811) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 811)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0811

/-! Kernel-checked entropy margins for general spectral rectangle 812. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0812
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4916991681, 4747007423, 4584563712, 4429236367, 4280630941, 4138380133, 4002141468, 3871595229, 3746442597, 3626403986, 3511217525, 3400637706, 3294434139, 3192390435, 3094303182, 2999981016, 2909243764, 2821921670, 2737854679, 2656891777, 2578890394, 2503715842, 2431240804, 2361344863, 2293914061, 2228840493, 2166021933, 2105361487, 2046767264, 1990152080, 1935433175, 1882531952, 1831373734, 1781887541, 1734005869, 1687664502, 1642802320, 1599361128, 1557285495, 1516522598, 1477022085, 1438735937, 1401618344, 1365625586, 1330715924, 1296849496, 1263988215, 1232095682, 1201137097, 1171079177, 1141890078, 1113539323, 1085997738, 1059237377, 1033231472, 1007954369, 983381474, 959489205, 936254937, 913656965, 891674450, 870287388, 849476563, 829223515, 809510501, 790320468, 771637014, 753444364, 735727338, 718471329, 701662270, 685286618, 669331325, 653783821, 638631988, 623864145, 609469027, 595435769, 581753886, 568413259, 555404120, 542717038, 530342902, 518272912, 506498560, 495011628, 483804167, 472868491, 462197165, 451782996, 441619024, 431698510, 422014931, 412561971, 403333510, 394323622, 385526561, 376936761, 368548826, 360357522, 352357775, 344544662, 336913407, 329459378, 322178075, 315065134, 308116316, 301327504, 294694700, 288214022, 281881696, 275694055, 269647537, 263738679, 257964112, 252320562, 246804845, 241413865, 236144609, 230994146, 225959623]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 812).prefactor = (2339163012765201/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 812).cutoff/(generalMeanRows 812).c)).2 =
    (88249550203013/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 812).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 812).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 812).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 812

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 812).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 812).criticalRate j.val*(generalMeanRows 812).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 812).c*(generalMeanRows 812).criticalPoint j.val)).2-
      (generalMeanRows 812).J/2-(generalMeanRows 812).error (generalMeanGrid j.val)+
      (generalMeanRows 812).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 812).c)).2-
      (generalMeanRows 812).J/2-(generalMeanRows 812).error 4 := by
  have he : (generalMeanRows 812).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 812) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 812)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0812

/-! Kernel-checked entropy margins for general spectral rectangle 813. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0813
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5058230901, 4887915580, 4725108676, 4569386482, 4420355084, 4277647766, 4140922685, 4009860796, 3884163990, 3763553414, 3647767965, 3536562917, 3429708684, 3326989693, 3228203360, 3133159155, 3041677746, 2953590221, 2868737366, 2786969013, 2708143426, 2632126753, 2558792503, 2488021077, 2419699326, 2353720144, 2289982094, 2228389054, 2168849898, 2111278189, 2055591901, 2001713158, 1949567987, 1899086096, 1850200656, 1802848107, 1756967969, 1712502673, 1669397396, 1627599908, 1587060430, 1547731504, 1509567861, 1472526310, 1436565620, 1401646423, 1367731113, 1334783754, 1302769991, 1271656974, 1241413277, 1212008827, 1183414834, 1155603730, 1128549104, 1102225649, 1076609105, 1051676206, 1027404636, 1003772983, 980760692, 958348025, 936516025, 915246479, 894521880, 874325397, 854640842, 835452645, 816745818, 798505937, 780719111, 763371959, 746451591, 729945583, 713841955, 698129157, 682796047, 667831873, 653226258, 638969184, 625050975, 611462286, 598194085, 585237645, 572584529, 560226575, 548155893, 536364844, 524846040, 513592328, 502596779, 491852687, 481353554, 471093082, 461065171, 451263904, 441683545, 432318534, 423163472, 414213126, 405462415, 396906406, 388540313, 380359486, 372359409, 364535696, 356884084, 349400433, 342080715, 334921017, 327917534, 321066564, 314364508, 307807863, 301393222, 295117269, 288976777, 282968602, 277089688, 271337053, 265707799]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 813).prefactor = (4674292047606109/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 813).cutoff/(generalMeanRows 813).c)).2 =
    (37025746160751/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 813).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 813).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 813).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 813

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 813).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 813).criticalRate j.val*(generalMeanRows 813).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 813).c*(generalMeanRows 813).criticalPoint j.val)).2-
      (generalMeanRows 813).J/2-(generalMeanRows 813).error (generalMeanGrid j.val)+
      (generalMeanRows 813).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 813).c)).2-
      (generalMeanRows 813).J/2-(generalMeanRows 813).error 4 := by
  have he : (generalMeanRows 813).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 813) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 813)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0813

/-! Kernel-checked entropy margins for general spectral rectangle 814. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0814
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4994196881, 4823750203, 4660847412, 4505063047, 4356001534, 4213294585, 4076598864, 3945593910, 3819980265, 3699477795, 3583824174, 3472773508, 3366095100, 3263572312, 3165001544, 3070191293, 2978961296, 2891141748, 2806572581, 2725102806, 2646589904, 2570899264, 2497903675, 2427482840, 2359522942, 2293916236, 2230560665, 2169359518, 2110221096, 2053058417, 1997788927, 1944334243, 1892619907, 1842575157, 1794132714, 1747228585, 1701801873, 1657794610, 1615151585, 1573820200, 1533750319, 1494894140, 1457206067, 1420642591, 1385162178, 1350725169, 1317293675, 1284831490, 1253304003, 1222678115, 1192922160, 1164005837, 1135900137, 1108577281, 1082010657, 1056174765, 1031045158, 1006598396, 982811993, 959664372, 937134825, 915203466, 893851197, 873059668, 852811245, 833088974, 813876551, 795158292, 776919106, 759144467, 741820388, 724933399, 708470523, 692419255, 676767538, 661503751, 646616681, 632095514, 617929811, 604109498, 590624845, 577466458, 564625259, 552092477, 539859635, 527918535, 516261250, 504880114, 493767708, 482916852, 472320596, 461972212, 451865182, 441993193, 432350129, 422930062, 413727247, 404736113, 395951256, 387367438, 378979574, 370782731, 362772123, 354943101, 347291152, 339811895, 332501074, 325354554, 318368316, 311538457, 304861182, 298332802, 291949728, 285708474, 279605645, 273637942, 267802153, 262095153, 256513902, 251055439, 245716881]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 814).prefactor = (4690762485900927/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 814).cutoff/(generalMeanRows 814).c)).2 =
    (362984702278429/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 814).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 814).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 814).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 814

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 814).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 814).criticalRate j.val*(generalMeanRows 814).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 814).c*(generalMeanRows 814).criticalPoint j.val)).2-
      (generalMeanRows 814).J/2-(generalMeanRows 814).error (generalMeanGrid j.val)+
      (generalMeanRows 814).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 814).c)).2-
      (generalMeanRows 814).J/2-(generalMeanRows 814).error 4 := by
  have he : (generalMeanRows 814).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 814) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 814)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0814

/-! Kernel-checked entropy margins for general spectral rectangle 815. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0815
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4934465338, 4763877002, 4600856010, 4444976673, 4295843144, 4153086816, 4016363995, 3885353830, 3759756440, 3639291243, 3523695442, 3412722651, 3306141666, 3203735326, 3105299498, 3010642136, 2919582428, 2831950016, 2747584273, 2666333651, 2588055072, 2512613370, 2439880776, 2369736444, 2302066010, 2236761188, 2173719389, 2112843372, 2054040921, 1997224542, 1942311180, 1889221960, 1837881941, 1788219886, 1740168056, 1693662005, 1648640395, 1605044824, 1562819666, 1521911909, 1482271022, 1443848815, 1406599316, 1370478650, 1335444928, 1301458148, 1268480087, 1236474217, 1205405613, 1175240875, 1145948046, 1117496541, 1089857079, 1063001620, 1036903297, 1011536366, 986876146, 962898970, 939582134, 916903854, 894843220, 873380154, 852495373, 832170350, 812387282, 793129053, 774379203, 756121901, 738341914, 721024581, 704155788, 687721941, 671709947, 656107191, 640901513, 626081189, 611634915, 597551787, 583821281, 570433246, 557377876, 544645708, 532227598, 520114713, 508298519, 496770766, 485523476, 474548938, 463839689, 453388511, 443188418, 433232650, 423514658, 414028105, 404766848, 395724941, 386896618, 378276293, 369858549, 361638135, 353609959, 345769080, 338110706, 330630187, 323323009, 316184791, 309211278, 302398340, 295741965, 289238256, 282883427, 276673797, 270605792, 264675935, 258880846, 253217241, 247681923, 242271785, 236983803, 231815036, 226762622]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 815).prefactor = (1173737882378287/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 815).cutoff/(generalMeanRows 815).c)).2 =
    (88249550203013/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 815).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 815).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 815).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 815

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 815).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 815).criticalRate j.val*(generalMeanRows 815).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 815).c*(generalMeanRows 815).criticalPoint j.val)).2-
      (generalMeanRows 815).J/2-(generalMeanRows 815).error (generalMeanGrid j.val)+
      (generalMeanRows 815).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 815).c)).2-
      (generalMeanRows 815).J/2-(generalMeanRows 815).error 4 := by
  have he : (generalMeanRows 815).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 815) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 815)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0815

/-! Kernel-checked entropy margins for general spectral rectangle 816. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0816
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4952001092, 4780806531, 4617206207, 4460772917, 4311109408, 4167845762, 4030637065, 3899161325, 3773117596, 3652224299, 3536217701, 3424850544, 3317890798, 3215120534, 3116334892, 3021341143, 2929957834, 2842013999, 2757348443, 2675809079, 2597252319, 2521542518, 2448551451, 2378157845, 2310246930, 2244710032, 2181444199, 2120351845, 2061340426, 2004322137, 1949213628, 1895935744, 1844413276, 1794574736, 1746352143, 1699680821, 1654499216, 1610748719, 1568373504, 1527320372, 1487538612, 1448979863, 1411597989, 1375348960, 1340190738, 1306083177, 1272987921, 1240868311, 1209689298, 1179417363, 1150020435, 1121467821, 1093730136, 1066779240, 1040588171, 1015131092, 990383237, 966320852, 942921154, 920162282, 898023250, 876483910, 855524910, 835127658, 815274287, 795947619, 777131137, 758808954, 740965781, 723586907, 706658167, 690165918, 674097023, 658438819, 643179103, 628306112, 613808500, 599675324, 585896024, 572460411, 559358646, 546581231, 534118990, 521963060, 510104875, 498536155, 487248895, 476235356, 465488049, 454999731, 444763390, 434772241, 425019715, 415499448, 406205280, 397131240, 388271544, 379620584, 371172926, 362923299, 354866593, 346997850, 339312260, 331805157, 324472012, 317308426, 310310131, 303472982, 296792952, 290266131, 283888718, 277657021, 271567452, 265616521, 259800839, 254117106, 248562118, 243132753, 237825980, 232638844, 227568475]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 816).prefactor = (2355818058017747/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 816).cutoff/(generalMeanRows 816).c)).2 =
    (88249550203013/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 816).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 816).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 816).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 816

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 816).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 816).criticalRate j.val*(generalMeanRows 816).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 816).c*(generalMeanRows 816).criticalPoint j.val)).2-
      (generalMeanRows 816).J/2-(generalMeanRows 816).error (generalMeanGrid j.val)+
      (generalMeanRows 816).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 816).c)).2-
      (generalMeanRows 816).J/2-(generalMeanRows 816).error 4 := by
  have he : (generalMeanRows 816).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 816) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 816)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0816

/-! Kernel-checked entropy margins for general spectral rectangle 817. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0817
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5258974505, 5091710673, 4931707128, 4778552583, 4631864811, 4491288110, 4356491028, 4227164343, 4103019237, 3983785663, 3869210864, 3759058041, 3653105138, 3551143744, 3452978093, 3358424146, 3267308763, 3179468933, 3094751079, 3013010411, 2934110336, 2857921914, 2784323356, 2713199557, 2644441672, 2577946716, 2513617196, 2451360773, 2391089942, 2332721740, 2276177469, 2221382446, 2168265762, 2116760060, 2066801330, 2018328718, 1971284339, 1925613116, 1881262614, 1838182901, 1796326401, 1755647771, 1716103773, 1677653164, 1640256588, 1603876472, 1568476935, 1534023696, 1500483993, 1467826499, 1436021254, 1405039589, 1374854065, 1345438406, 1316767444, 1288817062, 1261564142, 1234986514, 1209062914, 1183772934, 1159096984, 1135016252, 1111512666, 1088568860, 1066168140, 1044294453, 1022932354, 1002066984, 981684036, 961769736, 942310814, 923294484, 904708421, 886540742, 868779984, 851415089, 834435381, 817830556, 801590662, 785706084, 770167531, 754966020, 740092868, 725539674, 711298312, 697360915, 683719870, 670367802, 657297569, 644502251, 631975140, 619709736, 607699734, 595939017, 584421653, 573141884, 562094121, 551272938, 540673065, 530289382, 520116915, 510150830, 500386427, 490819139, 481444521, 472258250, 463256123, 454434047, 445788038, 437314219, 429008813, 420868145, 412888632, 405066783, 397399199, 389882565, 382513649, 375289303, 368206454, 361262107, 354453340]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 817).prefactor = (2286118069730219/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 817).cutoff/(generalMeanRows 817).c)).2 =
    (80157050254481/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 817).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 817).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 817).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 817

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 817).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 817).criticalRate j.val*(generalMeanRows 817).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 817).c*(generalMeanRows 817).criticalPoint j.val)).2-
      (generalMeanRows 817).J/2-(generalMeanRows 817).error (generalMeanGrid j.val)+
      (generalMeanRows 817).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 817).c)).2-
      (generalMeanRows 817).J/2-(generalMeanRows 817).error 4 := by
  have he : (generalMeanRows 817).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 817) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 817)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0817

/-! Kernel-checked entropy margins for general spectral rectangle 818. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0818
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5124194276, 4956462192, 4796062451, 4642580509, 4495631053, 4354855453, 4219919475, 4090511247, 3966339431, 3847131571, 3732632614, 3622603563, 3516820260, 3415072282, 3317161933, 3222903324, 3132121539, 3044651861, 2960339074, 2879036811, 2800606963, 2724919130, 2651850118, 2581283469, 2513109033, 2447222566, 2383525366, 2321923922, 2262329602, 2204658355, 2148830434, 2094770140, 2042405588, 1991668475, 1942493880, 1894820067, 1848588303, 1803742687, 1760229994, 1717999524, 1677002963, 1637194253, 1598529467, 1560966697, 1524465942, 1488989010, 1454499420, 1420962315, 1388344371, 1356613726, 1325739898, 1295693719, 1266447264, 1237973792, 1210247685, 1183244393, 1156940380, 1131313074, 1106340822, 1082002843, 1058279189, 1035150700, 1012598973, 990606321, 969155741, 948230885, 927816024, 907896025, 888456320, 869482882, 850962201, 832881258, 815227507, 797988853, 781153629, 764710583, 748648854, 732957959, 717627776, 702648529, 688010773, 673705379, 659723523, 646056671, 632696571, 619635237, 606864942, 594378203, 582167777, 570226649, 558548022, 547125307, 535952121, 525022275, 514329764, 503868766, 493633631, 483618877, 473819182, 464229378, 454844448, 445659517, 436669850, 427870845, 419258029, 410827054, 402573693, 394493833, 386583476, 378838728, 371255805, 363831020, 356560786, 349441611, 342470092, 335642917, 328956860, 322408776, 315995603, 309714354, 303562119]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 818).prefactor = (184165334187283/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 818).cutoff/(generalMeanRows 818).c)).2 =
    (386079103882709/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 818).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 818).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 818).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 818

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 818).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 818).criticalRate j.val*(generalMeanRows 818).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 818).c*(generalMeanRows 818).criticalPoint j.val)).2-
      (generalMeanRows 818).J/2-(generalMeanRows 818).error (generalMeanGrid j.val)+
      (generalMeanRows 818).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 818).c)).2-
      (generalMeanRows 818).J/2-(generalMeanRows 818).error 4 := by
  have he : (generalMeanRows 818).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 818) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 818)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0818

/-! Kernel-checked entropy margins for general spectral rectangle 819. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0819
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5169217093, 5002367191, 4842809580, 4690129814, 4543942778, 4403890120, 4269637968, 4140874882, 4017310017, 3898671471, 3784704788, 3675171617, 3569848483, 3468525678, 3371006248, 3277105074, 3186648024, 3099471186, 3015420158, 2934349398, 2856121628, 2780607285, 2707684007, 2637236176, 2569154472, 2503335484, 2439681328, 2378099313, 2318501611, 2260804969, 2204930427, 2150803061, 2098351746, 2047508931, 1998210431, 1950395229, 1904005301, 1858985437, 1815283090, 1772848221, 1731633163, 1691592487, 1652682882, 1614863038, 1578093539, 1542336760, 1507556773, 1473719256, 1440791409, 1408741874, 1377540663, 1347159083, 1317569672, 1288746137, 1260663294, 1233297012, 1206624162, 1180622566, 1155270949, 1130548900, 1106436822, 1082915902, 1059968064, 1037575941, 1015722839, 994392704, 973570095, 953240151, 933388571, 914001582, 895065919, 876568799, 858497902, 840841350, 823587686, 806725855, 790245191, 774135395, 758386521, 742988961, 727933431, 713210959, 698812867, 684730763, 670956530, 657482310, 644300498, 631403730, 618784873, 606437018, 594353467, 582527730, 570953513, 559624711, 548535404, 537679845, 527052458, 516647828, 506460699, 496485964, 486718662, 477153972, 467787210, 458613822, 449629377, 440829568, 432210207, 423767215, 415496626, 407394577, 399457310, 391681163, 384062572, 376598064, 369284255, 362117849, 355095633, 348214475, 341471322, 334863196, 328387196]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 819).prefactor = (2298073853629751/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 819).cutoff/(generalMeanRows 819).c)).2 =
    (1595659199143/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 819).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 819).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 819).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 819

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 819).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 819).criticalRate j.val*(generalMeanRows 819).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 819).c*(generalMeanRows 819).criticalPoint j.val)).2-
      (generalMeanRows 819).J/2-(generalMeanRows 819).error (generalMeanGrid j.val)+
      (generalMeanRows 819).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 819).c)).2-
      (generalMeanRows 819).J/2-(generalMeanRows 819).error 4 := by
  have he : (generalMeanRows 819).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 819) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 819)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0819

/-! Kernel-checked entropy margins for general spectral rectangle 820. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0820
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5119546725, 4951917035, 4791640225, 4638298805, 4491504800, 4350897171, 4216139513, 4086917998, 3962939525, 3843930058, 3729633126, 3619808461, 3514230775, 3412688635, 3314983450, 3220928543, 3130348300, 3043077394, 2958960075, 2877849518, 2799607218, 2724102436, 2651211695, 2580818301, 2512811912, 2447088134, 2383548145, 2322098352, 2262650065, 2205119204, 2149426015, 2095494813, 2043253743, 1992634553, 1943572383, 1896005571, 1849875470, 1805126275, 1761704864, 1719560648, 1678645428, 1638913267, 1600320363, 1562824936, 1526387116, 1490968842, 1456533767, 1423047166, 1390475850, 1358788091, 1327953538, 1297943155, 1268729147, 1240284903, 1212584929, 1185604802, 1159321105, 1133711389, 1108754117, 1084428622, 1060715067, 1037594404, 1015048334, 993059273, 971610320, 950685223, 930268348, 910344654, 890899660, 871919427, 853390525, 835300018, 817635437, 800384758, 783536390, 767079147, 751002236, 735295238, 719948092, 704951081, 690294816, 675970223, 661968530, 648281253, 634900187, 621817392, 609025184, 596516123, 584283005, 572318853, 560616904, 549170608, 537973612, 527019757, 516303070, 505817757, 495558194, 485518925, 475694651, 466080227, 456670658, 447461089, 438446805, 429623221, 420985882, 412530456, 404252731, 396148608, 388214101, 380445332, 372838526, 365390007, 358096199, 350953618, 343958873, 337108657, 330399752, 323829021, 317393406, 311089929, 304915685]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 820).prefactor = (1156918908217309/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 820).cutoff/(generalMeanRows 820).c)).2 =
    (391588759693677/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 820).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 820).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 820).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 820

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 820).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 820).criticalRate j.val*(generalMeanRows 820).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 820).c*(generalMeanRows 820).criticalPoint j.val)).2-
      (generalMeanRows 820).J/2-(generalMeanRows 820).error (generalMeanGrid j.val)+
      (generalMeanRows 820).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 820).c)).2-
      (generalMeanRows 820).J/2-(generalMeanRows 820).error 4 := by
  have he : (generalMeanRows 820).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 820) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 820)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0820

/-! Kernel-checked entropy margins for general spectral rectangle 821. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0821
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5076315066, 4907814596, 4746707727, 4592576790, 4445033540, 4303716584, 4168289093, 4038436744, 3913865886, 3794301876, 3679487591, 3569182075, 3463159311, 3361207110, 3263126100, 3168728800, 3077838774, 2990289865, 2905925476, 2824597932, 2746167869, 2670503693, 2597481068, 2526982444, 2458896628, 2393118379, 2329548038, 2268091181, 2208658301, 2151164506, 2095529245, 2041676051, 1989532296, 1939028971, 1890100474, 1842684417, 1796721440, 1752155041, 1708931417, 1666999316, 1626309889, 1586816568, 1548474935, 1511242609, 1475079138, 1439945893, 1405805976, 1372624125, 1340366634, 1309001267, 1278497187, 1248824882, 1219956099, 1191863781, 1164522007, 1137905933, 1111991745, 1086756601, 1062178591, 1038236685, 1014910696, 992181238, 970029686, 948438145, 927389411, 906866940, 886854819, 867337737, 848300956, 829730286, 811612060, 793933111, 776680750, 759842743, 743407295, 727363027, 711698959, 696404495, 681469405, 666883807, 652638157, 638723234, 625130123, 611850206, 598875149, 586196889, 573807625, 561699807, 549866126, 538299504, 526993085, 515940227, 505134493, 494569645, 484239633, 474138591, 464260829, 454600827, 445153227, 435912830, 426874586, 418033594, 409385093, 400924456, 392647190, 384548927, 376625420, 368872543, 361286281, 353862731, 346598094, 339488677, 332530884, 325721216, 319056266, 312532719, 306147346, 299897000, 293778620, 287789221, 281925896]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 821).prefactor = (927250618783551/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 821).cutoff/(generalMeanRows 821).c)).2 =
    (37880634455363/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 821).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 821).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 821).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 821

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 821).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 821).criticalRate j.val*(generalMeanRows 821).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 821).c*(generalMeanRows 821).criticalPoint j.val)).2-
      (generalMeanRows 821).J/2-(generalMeanRows 821).error (generalMeanGrid j.val)+
      (generalMeanRows 821).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 821).c)).2-
      (generalMeanRows 821).J/2-(generalMeanRows 821).error 4 := by
  have he : (generalMeanRows 821).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 821) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 821)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0821

/-! Kernel-checked entropy margins for general spectral rectangle 822. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0822
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5029279326, 4860039422, 4698254393, 4543503397, 4395395210, 4253565642, 4117675225, 3987407152, 3862465423, 3742573181, 3627471204, 3516916548, 3410681312, 3308551521, 3210326106, 3115815970, 3024843145, 2937240011, 2852848582, 2771519854, 2693113201, 2617495822, 2544542227, 2474133768, 2406158198, 2340509273, 2277086372, 2215794150, 2156542221, 2099244850, 2043820679, 1990192468, 1938286847, 1888034099, 1839367941, 1792225331, 1746546284, 1702273699, 1659353196, 1617732971, 1577363646, 1538198144, 1500191560, 1463301044, 1427485694, 1392706451, 1358926002, 1326108691, 1294220426, 1263228609, 1233102051, 1203810902, 1175326588, 1147621740, 1120670140, 1094446660, 1068927210, 1044088689, 1019908931, 996366669, 973441483, 951113766, 929364681, 908176130, 887530712, 867411701, 847803003, 828689137, 810055203, 791886855, 774170276, 756892158, 740039676, 723600467, 707562611, 691914613, 676645381, 661744210, 647200770, 633005082, 619147512, 605618749, 592409798, 579511960, 566916829, 554616271, 542602420, 530867662, 519404629, 508206188, 497265432, 486575668, 476130415, 465923392, 455948508, 446199862, 436671727, 427358553, 418254952, 409355698, 400655717, 392150085, 383834020, 375702879, 367752150, 359977451, 352374525, 344939232, 337667549, 330555566, 323599478, 316795587, 310140295, 303630099, 297261595, 291031466, 284936485, 278973512, 273139486, 267431429, 261846441]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 822).prefactor = (933719381911613/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 822).cutoff/(generalMeanRows 822).c)).2 =
    (185793048290071/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 822).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 822).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 822).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 822

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 822).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 822).criticalRate j.val*(generalMeanRows 822).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 822).c*(generalMeanRows 822).criticalPoint j.val)).2-
      (generalMeanRows 822).J/2-(generalMeanRows 822).error (generalMeanGrid j.val)+
      (generalMeanRows 822).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 822).c)).2-
      (generalMeanRows 822).J/2-(generalMeanRows 822).error 4 := by
  have he : (generalMeanRows 822).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 822) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 822)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0822

/-! Kernel-checked entropy margins for general spectral rectangle 823. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0823
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5080940282, 4912365862, 4751162827, 4596916518, 4449241415, 4307778595, 4172193461, 4042173708, 3917427502, 3797681843, 3682681080, 3572185580, 3465970511, 3363824745, 3265549854, 3170959195, 3079877077, 2992137996, 2907585932, 2826073712, 2747462410, 2671620808, 2598424889, 2527757377, 2459507304, 2393569615, 2329844799, 2268238548, 2208661439, 2151028637, 2095259627, 2041277951, 1989010976, 1938389665, 1889348379, 1841824672, 1795759119, 1751095144, 1707778857, 1665758911, 1624986360, 1585414529, 1546998888, 1509696944, 1473468127, 1438273687, 1404076605, 1370841497, 1338534532, 1307123352, 1276576995, 1246865826, 1217961471, 1189836751, 1162465625, 1135823134, 1109885344, 1084629302, 1060032984, 1036075251, 1012735811, 989995170, 967834604, 946236115, 925182404, 904656833, 884643398, 865126697, 846091908, 827524756, 809411494, 791738877, 774494139, 757664976, 741239521, 725206326, 709554348, 694272927, 679351771, 664780942, 650550841, 636652190, 623076024, 609813677, 596856765, 584197182, 571827083, 559738876, 547925213, 536378977, 525093276, 514061434, 503276982, 492733648, 482425355, 472346207, 462490488, 452852652, 443427316, 434209257, 425193407, 416374841, 407748778, 399310575, 391055720, 382979828, 375078638, 367348008, 359783910, 352382428, 345139752, 338052175, 331116093, 324327995, 317684468, 311182185, 304817909, 298588490, 292490855, 286522016, 280679058]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 823).prefactor = (4612255327749571/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 823).cutoff/(generalMeanRows 823).c)).2 =
    (93331719697251/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 823).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 823).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 823).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 823

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 823).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 823).criticalRate j.val*(generalMeanRows 823).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 823).c*(generalMeanRows 823).criticalPoint j.val)).2-
      (generalMeanRows 823).J/2-(generalMeanRows 823).error (generalMeanGrid j.val)+
      (generalMeanRows 823).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 823).c)).2-
      (generalMeanRows 823).J/2-(generalMeanRows 823).error 4 := by
  have he : (generalMeanRows 823).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 823) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 823)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0823

/-! Kernel-checked entropy margins for general spectral rectangle 824. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0824
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5034835328, 4865501940, 4703601872, 4548717260, 4400459573, 4258467060, 4122402458, 3991950950, 3866818332, 3746729363, 3631426273, 3520667420, 3414226072, 3311889294, 3213456942, 3118740746, 3027563463, 2939758116, 2855167280, 2773642441, 2695043399, 2619237715, 2546100211, 2475512500, 2407362553, 2341544301, 2277957262, 2216506199, 2157100802, 2099655386, 2044088622, 1990323271, 1938285952, 1887906915, 1839119832, 1791861600, 1746072163, 1701694339, 1658673659, 1616958218, 1576498537, 1537247426, 1499159866, 1462192891, 1426305477, 1391458441, 1357614346, 1324737408, 1292793412, 1261749630, 1231574747, 1202238790, 1173713057, 1145970058, 1118983452, 1092727991, 1067179468, 1042314663, 1018111299, 994547995, 971604225, 949260272, 927497199, 906296802, 885641587, 865514728, 845900040, 826781951, 808145473, 789976176, 772260161, 754984041, 738134912, 721700340, 705668333, 690027324, 674766158, 659874065, 645340653, 631155885, 617310069, 603793840, 590598149, 577714250, 565133686, 552848278, 540850114, 529131541, 517685148, 506503765, 495580445, 484908464, 474481305, 464292655, 454336393, 444606588, 435097487, 425803512, 416719252, 407839455, 399159026, 390673020, 382376634, 374265205, 366334206, 358579235, 350996020, 343580407, 336328358, 329235948, 322299361, 315514887, 308878917, 302387938, 296038534, 289827382, 283751246, 277806976, 271991507, 266301852, 260735105]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 824).prefactor = (4644986203944291/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 824).cutoff/(generalMeanRows 824).c)).2 =
    (183053315407759/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 824).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 824).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 824).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 824

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 824).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 824).criticalRate j.val*(generalMeanRows 824).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 824).c*(generalMeanRows 824).criticalPoint j.val)).2-
      (generalMeanRows 824).J/2-(generalMeanRows 824).error (generalMeanGrid j.val)+
      (generalMeanRows 824).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 824).c)).2-
      (generalMeanRows 824).J/2-(generalMeanRows 824).error 4 := by
  have he : (generalMeanRows 824).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 824) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 824)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0824

/-! Kernel-checked entropy margins for general spectral rectangle 825. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0825
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4995085911, 4824955621, 4662297389, 4506693133, 4357754028, 4215117949, 4078447196, 3947426454, 3821760967, 3701174895, 3585409827, 3474223445, 3367388307, 3264690741, 3165929847, 3070916573, 2979472887, 2891431002, 2806632683, 2724928593, 2646177707, 2570246762, 2497009754, 2426347474, 2358147075, 2292301674, 2228709987, 2167275981, 2107908558, 2050521258, 1995031987, 1941362757, 1889439446, 1839191581, 1790552120, 1743457267, 1697846284, 1653661322, 1610847262, 1569351563, 1529124125, 1490117158, 1452285052, 1415584269, 1379973228, 1345412206, 1311863239, 1279290034, 1247657879, 1216933569, 1187085321, 1158082713, 1129896606, 1102499089, 1075863411, 1049963931, 1024776060, 1000276212, 976441753, 953250961, 930682977, 908717770, 887336093, 866519450, 846250060, 826510826, 807285301, 788557661, 770312675, 752535681, 735212557, 718329704, 701874013, 685832853, 670194045, 654945845, 640076923, 625576349, 611433573, 597638410, 584181026, 571051920, 558241916, 545742145, 533544033, 521639292, 510019907, 498678123, 487606439, 476797593, 466244558, 455940528, 445878915, 436053333, 426457600, 417085722, 407931888, 398990469, 390256002, 381723191, 373386897, 365242136, 357284070, 349508003, 341909376, 334483762, 327226863, 320134502, 313202624, 306427286, 299804657, 293331014, 287002736, 280816304, 274768295, 268855381, 263074321, 257421966, 251895250, 246491189, 241206879]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 825).prefactor = (4653891647809653/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 825).cutoff/(generalMeanRows 825).c)).2 =
    (353488536569337/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 825).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 825).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 825).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 825

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 825).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 825).criticalRate j.val*(generalMeanRows 825).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 825).c*(generalMeanRows 825).criticalPoint j.val)).2-
      (generalMeanRows 825).J/2-(generalMeanRows 825).error (generalMeanGrid j.val)+
      (generalMeanRows 825).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 825).c)).2-
      (generalMeanRows 825).J/2-(generalMeanRows 825).error 4 := by
  have he : (generalMeanRows 825).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 825) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 825)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0825

/-! Kernel-checked entropy margins for general spectral rectangle 826. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0826
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4951527183, 4780672012, 4617351517, 4461144279, 4311658343, 4168528644, 4031414712, 3899998626, 3773983169, 3653090175, 3537059036, 3425645356, 3318619720, 3215766590, 3116883293, 3021779095, 2930274363, 2842199792, 2757395696, 2675711365, 2597004458, 2521140465, 2447992187, 2377439278, 2309367805, 2243669851, 2180243141, 2118990695, 2059820514, 2002645274, 1947382054, 1893952077, 1842280467, 1792296025, 1743931021, 1697120995, 1651804576, 1607923308, 1565421493, 1524246033, 1484346297, 1445673982, 1408182994, 1371829326, 1336570950, 1302367713, 1269181243, 1236974852, 1205713455, 1175363482, 1145892811, 1117270685, 1089467654, 1062455501, 1036207189, 1010696799, 985899479, 961791389, 938349655, 915552323, 893378315, 871807387, 850820093, 830397745, 810522379, 791176723, 772344165, 754008720, 736155008, 718768223, 701834108, 685338930, 669269460, 653612949, 638357107, 623490083, 609000450, 594877182, 581109638, 567687551, 554601006, 541840428, 529396570, 517260496, 505423570, 493877446, 482614054, 471625587, 460904498, 450443480, 440235466, 430273611, 420551293, 411062094, 401799801, 392758395, 383932041, 375315088, 366902053, 358687623, 350666646, 342834123, 335185206, 327715189, 320419506, 313293726, 306333546, 299534787, 292893393, 286405422, 280067045, 273874543, 267824300, 261912802, 256136634, 250492474, 244977094, 239587353, 234320197, 229172653, 224141831]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 826).prefactor = (585936878256543/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 826).cutoff/(generalMeanRows 826).c)).2 =
    (86592767200119/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 826).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 826).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 826).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 826

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 826).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 826).criticalRate j.val*(generalMeanRows 826).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 826).c*(generalMeanRows 826).criticalPoint j.val)).2-
      (generalMeanRows 826).J/2-(generalMeanRows 826).error (generalMeanGrid j.val)+
      (generalMeanRows 826).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 826).c)).2-
      (generalMeanRows 826).J/2-(generalMeanRows 826).error 4 := by
  have he : (generalMeanRows 826).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 826) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 826)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0826

/-! Kernel-checked entropy margins for general spectral rectangle 827. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0827
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4989545308, 4819480734, 4656911419, 4501416244, 4352603627, 4210108944, 4073592231, 3942736124, 3817244016, 3696838393, 3581259340, 3470263181, 3363621256, 3261118802, 3162553942, 3067736755, 2976488434, 2888640508, 2804034135, 2722519449, 2643954959, 2568207001, 2495149222, 2424662116, 2356632585, 2290953540, 2227523524, 2166246367, 2107030865, 2049790482, 1994443070, 1940910611, 1889118975, 1838997695, 1790479755, 1743501398, 1698001938, 1653923587, 1611211299, 1569812616, 1529677525, 1490758330, 1453009523, 1416387669, 1380851296, 1346360792, 1312878307, 1280367661, 1248794262, 1218125019, 1188328268, 1159373703, 1131232303, 1103876271, 1077278973, 1051414881, 1026259518, 1001789407, 977982024, 954815753, 932269841, 910324356, 888960153, 868158834, 847902711, 828174782, 808958687, 790238692, 771999651, 754226983, 736906649, 720025123, 703569375, 687526844, 671885422, 656633433, 641759612, 627253091, 613103382, 599300358, 585834240, 572695583, 559875262, 547364458, 535154645, 523237581, 511605294, 500250072, 489164455, 478341219, 467773373, 457454149, 447376990, 437535545, 427923660, 418535371, 409364897, 400406632, 391655141, 383105151, 374751547, 366589366, 358613789, 350820141, 343203882, 335760602, 328486019, 321375972, 314426421, 307633436, 300993200, 294502001, 288156232, 281952382, 275887040, 269956886, 264158691, 258489311, 252945688, 247524847, 242223889]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 827).prefactor = (935589870969271/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 827).cutoff/(generalMeanRows 827).c)).2 =
    (44867267667113/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 827).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 827).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 827).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 827

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 827).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 827).criticalRate j.val*(generalMeanRows 827).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 827).c*(generalMeanRows 827).criticalPoint j.val)).2-
      (generalMeanRows 827).J/2-(generalMeanRows 827).error (generalMeanGrid j.val)+
      (generalMeanRows 827).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 827).c)).2-
      (generalMeanRows 827).J/2-(generalMeanRows 827).error 4 := by
  have he : (generalMeanRows 827).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 827) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 827)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0827

/-! Kernel-checked entropy margins for general spectral rectangle 828. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0828
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4866819579, 4696580917, 4533907604, 4378374893, 4229587768, 4087178358, 3950803619, 3820143264, 3694897909, 3574787400, 3459549306, 3348937557, 3242721210, 3140683322, 3042619937, 2948339146, 2857660241, 2770412936, 2686436649, 2605579851, 2527699458, 2452660277, 2380334496, 2310601206, 2243345965, 2178460395, 2115841803, 2055392835, 1997021150, 1940639120, 1886163553, 1833515424, 1782619640, 1733404811, 1685803034, 1639749700, 1595183306, 1552045284, 1510279834, 1469833778, 1430656413, 1392699380, 1355916537, 1320263840, 1285699234, 1252182548, 1219675399, 1188141094, 1157544551, 1127852209, 1099031958, 1071053062, 1043886090, 1017502855, 991876349, 966980687, 942791052, 919283644, 896435629, 874225098, 852631017, 831633190, 811212218, 791349463, 772027011, 753227642, 734934796, 717132543, 699805555, 682939081, 666518919, 650531390, 634963322, 619802021, 605035252, 590651222, 576638558, 562986290, 549683835, 536720979, 524087865, 511774973, 499773111, 488073399, 476667257, 465546393, 454702791, 444128700, 433816626, 423759318, 413949760, 404381163, 395046955, 385940775, 377056460, 368388044, 359929744, 351675959, 343621261, 335760386, 328088231, 320599850, 313290444, 306155357, 299190073, 292390210, 285751512, 279269851, 272941218, 266761719, 260727572, 254835106, 249080751, 243461040, 237972604, 232612168, 227376548, 222262649, 217267461, 212388057, 207621590]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 828).prefactor = (2355573214396773/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 828).cutoff/(generalMeanRows 828).c)).2 =
    (344753506344949/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 828).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 828).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 828).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 828

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 828).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 828).criticalRate j.val*(generalMeanRows 828).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 828).c*(generalMeanRows 828).criticalPoint j.val)).2-
      (generalMeanRows 828).J/2-(generalMeanRows 828).error (generalMeanGrid j.val)+
      (generalMeanRows 828).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 828).c)).2-
      (generalMeanRows 828).J/2-(generalMeanRows 828).error 4 := by
  have he : (generalMeanRows 828).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 828) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 828)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0828

/-! Kernel-checked entropy margins for general spectral rectangle 829. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0829
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5290737174, 5123862793, 4964199710, 4811339785, 4664903730, 4524538584, 4389915464, 4260727550, 4136688276, 4017529707, 3903001069, 3792867424, 3686908466, 3584917431, 3486700100, 3392073893, 3300867042, 3212917829, 3128073895, 3046191601, 2967135435, 2890777480, 2816996909, 2745679529, 2676717352, 2610008202, 2545455353, 2482967184, 2422456873, 2363842099, 2307044773, 2251990782, 2198609759, 2146834858, 2096602549, 2047852433, 2000527053, 1954571736, 1909934431, 1866565561, 1824417892, 1783446397, 1743608142, 1704862165, 1667169377, 1630492455, 1594795754, 1560045216, 1526208284, 1493253829, 1461152073, 1429874520, 1399393891, 1369684062, 1340720004, 1312477734, 1284934255, 1258067515, 1231856352, 1206280462, 1181320344, 1156957274, 1133173258, 1109951005, 1087273887, 1065125913, 1043491697, 1022356430, 1001705854, 981526239, 961804353, 942527445, 923683224, 905259833, 887245836, 869630194, 852402253, 835551724, 819068668, 802943481, 787166882, 771729894, 756623838, 741840317, 727371204, 713208633, 699344986, 685772885, 672485183, 659474953, 646735479, 634260251, 622042953, 610077458, 598357821, 586878271, 575633205, 564617181, 553824914, 543251267, 532891251, 522740013, 512792835, 503045132, 493492439, 484130416, 474954837, 465961591, 457146673, 448506186, 440036333, 431733415, 423593829, 415614064, 407790698, 400120393, 392599899, 385226042, 377995730, 370905944, 363953741]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 829).prefactor = (456914611581671/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 829).cutoff/(generalMeanRows 829).c)).2 =
    (50437369643/125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 829).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 829).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 829).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 829

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 829).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 829).criticalRate j.val*(generalMeanRows 829).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 829).c*(generalMeanRows 829).criticalPoint j.val)).2-
      (generalMeanRows 829).J/2-(generalMeanRows 829).error (generalMeanGrid j.val)+
      (generalMeanRows 829).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 829).c)).2-
      (generalMeanRows 829).J/2-(generalMeanRows 829).error 4 := by
  have he : (generalMeanRows 829).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 829) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 829)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0829

/-! Kernel-checked entropy margins for general spectral rectangle 830. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0830
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5240736811, 5073020191, 4912576334, 4758994071, 4611891270, 4470912294, 4335725740, 4206022410, 4081513492, 3961928926, 3847015927, 3736537650, 3630271980, 3528010433, 3429557155, 3334728012, 3243349755, 3155259254, 3070302803, 2988335476, 2909220535, 2832828889, 2759038590, 2687734368, 2618807208, 2552153950, 2487676922, 2425283601, 2364886295, 2306401851, 2249751380, 2194860003, 2141656614, 2090073659, 2040046929, 1991515367, 1944420891, 1898708221, 1854324722, 1811220260, 1769347059, 1728659577, 1689114377, 1650670018, 1613286947, 1576927397, 1541555292, 1507136161, 1473637050, 1441026445, 1409274199, 1378351460, 1348230606, 1318885183, 1290289844, 1262420300, 1235253258, 1208766381, 1182938236, 1157748252, 1133176677, 1109204540, 1085813614, 1062986378, 1040705989, 1018956245, 997721558, 976986925, 956737901, 936960574, 917641542, 898767888, 880327158, 862307345, 844696862, 827484532, 810659563, 794211535, 778130385, 762406389, 747030149, 731992581, 717284898, 702898601, 688825468, 675057538, 661587108, 648406712, 635509124, 622887339, 610534568, 598444229, 586609942, 575025514, 563684941, 552582394, 541712214, 531068910, 520647146, 510441740, 500447658, 490660007, 481074029, 471685102, 462488729, 453480535, 444656266, 436011781, 427543051, 419246153, 411117268, 403152677, 395348757, 387701981, 380208910, 372866193, 365670566, 358618845, 351707926, 344934784, 338296467]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 830).prefactor = (4600894279187713/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 830).cutoff/(generalMeanRows 830).c)).2 =
    (396199654662389/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 830).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 830).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 830).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 830

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 830).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 830).criticalRate j.val*(generalMeanRows 830).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 830).c*(generalMeanRows 830).criticalPoint j.val)).2-
      (generalMeanRows 830).J/2-(generalMeanRows 830).error (generalMeanGrid j.val)+
      (generalMeanRows 830).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 830).c)).2-
      (generalMeanRows 830).J/2-(generalMeanRows 830).error 4 := by
  have he : (generalMeanRows 830).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 830) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 830)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0830

/-! Kernel-checked entropy margins for general spectral rectangle 831. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0831
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4937682576, 4767047367, 4603989511, 4448081687, 4298926587, 4156154299, 4019419972, 3888401726, 3762798772, 3642329728, 3526731095, 3415755878, 3309172339, 3206762864, 3108322927, 3013660152, 2922593450, 2834952235, 2750575696, 2669312140, 2591018378, 2515559165, 2442806679, 2372640049, 2304944905, 2239612974, 2176541695, 2115633875, 2056797354, 1999944705, 1944992950, 1891863298, 1840480898, 1790774612, 1742676797, 1696123110, 1651052320, 1607406132, 1565129023, 1524168093, 1484472914, 1445995405, 1408689695, 1372512014, 1337420575, 1303375471, 1270338578, 1238273461, 1207145285, 1176920736, 1147567944, 1119056403, 1091356912, 1064441503, 1038283382, 1012856873, 988137359, 964101235, 940725855, 917989490, 895871281, 874351199, 853410007, 833029222, 813191077, 793878495, 775075051, 756764944, 738932971, 721564496, 704645429, 688162200, 672101734, 656451432, 641199149, 626333177, 611842222, 597715388, 583942161, 570512394, 557416288, 544644381, 532187531, 520036907, 508183972, 496620475, 485338435, 474330135, 463588109, 453105132, 442874210, 432888575, 423141672, 413627150, 404338861, 395270845, 386417326, 377772705, 369331555, 361088612, 353038769, 345177074, 337498720, 329999043, 322673515, 315517740, 308527451, 301698502, 295026865, 288508629, 282139992, 275917260, 269836842, 263895246, 258089079, 252415039, 246869916, 241450587, 236154014, 230977241, 225917390]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 831).prefactor = (1183490758460023/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 831).cutoff/(generalMeanRows 831).c)).2 =
    (44662517416583/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 831).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 831).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 831).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 831

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 831).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 831).criticalRate j.val*(generalMeanRows 831).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 831).c*(generalMeanRows 831).criticalPoint j.val)).2-
      (generalMeanRows 831).J/2-(generalMeanRows 831).error (generalMeanGrid j.val)+
      (generalMeanRows 831).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 831).c)).2-
      (generalMeanRows 831).J/2-(generalMeanRows 831).error 4 := by
  have he : (generalMeanRows 831).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 831) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 831)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0831

/-! Kernel-checked entropy margins for general spectral rectangle 832. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0832
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5255871993, 5081411406, 4914605944, 4755023164, 4602261086, 4455945537, 4315727771, 4181282348, 4052305230, 3928512061, 3809636622, 3695429433, 3585656483, 3480098079, 3378547796, 3280811521, 3186706578, 3096060931, 3008712447, 2924508224, 2843303972, 2764963440, 2689357894, 2616365628, 2545871514, 2477766589, 2411947669, 2348316990, 2286781879, 2227254441, 2169651278, 2113893214, 2059905056, 2007615353, 1956956181, 1907862947, 1860274189, 1814131410, 1769378901, 1725963598, 1683834925, 1642944665, 1603246831, 1564697541, 1527254914, 1490878953, 1455531455, 1421175913, 1387777425, 1355302618, 1323719563, 1292997703, 1263107788, 1234021803, 1205712908, 1178155384, 1151324572, 1125196823, 1099749451, 1074960684, 1050809619, 1027276186, 1004341101, 981985834, 960192574, 938944192, 918224213, 898016782, 878306642, 859079099, 840320004, 822015724, 804153120, 786719528, 769702733, 753090955, 736872826, 721037374, 705574006, 690472494, 675722954, 661315839, 647241919, 633492272, 620058267, 606931557, 594104067, 581567977, 569315721, 557339970, 545633626, 534189812, 523001863, 512063320, 501367920, 490909589, 480682435, 470680744, 460898969, 451331725, 441973785, 432820074, 423865662, 415105760, 406535714, 398151003, 389947230, 381920122, 374065522, 366379389, 358857792, 351496904, 344293003, 337242467, 330341768, 323587473, 316976239, 310504810, 304170014, 297968760, 291898040]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 832).prefactor = (2400122182307437/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 832).cutoff/(generalMeanRows 832).c)).2 =
    (37880634455363/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 832).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 832).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 832).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 832

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 832).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 832).criticalRate j.val*(generalMeanRows 832).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 832).c*(generalMeanRows 832).criticalPoint j.val)).2-
      (generalMeanRows 832).J/2-(generalMeanRows 832).error (generalMeanGrid j.val)+
      (generalMeanRows 832).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 832).c)).2-
      (generalMeanRows 832).J/2-(generalMeanRows 832).error 4 := by
  have he : (generalMeanRows 832).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 832) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 832)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0832

/-! Kernel-checked entropy margins for general spectral rectangle 833. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0833
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5286811741, 5120050526, 4960519613, 4807808038, 4661533963, 4521342126, 4386901569, 4257903604, 4134059986, 4015101276, 3900775351, 3790846069, 3685092052, 3583305584, 3485291602, 3390866784, 3299858708, 3212105088, 3127453070, 3045758587, 2966885766, 2890706381, 2817099349, 2745950266, 2677150975, 2610599170, 2546198028, 2483855863, 2423485812, 2365005540, 2308336966, 2253406004, 2200142330, 2148479157, 2098353030, 2049703631, 2002473601, 1956608367, 1912055989, 1868767008, 1826694313, 1785793002, 1746020271, 1707335292, 1669699108, 1633074534, 1597426061, 1562719766, 1528923232, 1496005463, 1463936817, 1432688931, 1402234659, 1372548005, 1343604071, 1315378998, 1287849912, 1260994882, 1234792865, 1209223670, 1184267912, 1159906973, 1136122969, 1112898709, 1090217668, 1068063952, 1046422270, 1025277905, 1004616687, 984424970, 964689607, 945397928, 926537717, 908097191, 890064987, 872430134, 855182045, 838310494, 821805603, 805657827, 789857941, 774397023, 759266445, 744457860, 729963187, 715774606, 701884542, 688285660, 674970851, 661933225, 649166104, 636663009, 624417658, 612423956, 600675987, 589168006, 577894437, 566849865, 556029026, 545426808, 535038241, 524858492, 514882865, 505106789, 495525819, 486135628, 476932007, 467910857, 459068188, 450400113, 441902848, 433572704, 425406088, 417399498, 409549520, 401852826, 394306170, 386906387, 379650390, 372535166, 365557776]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 833).prefactor = (4591678009207839/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 833).cutoff/(generalMeanRows 833).c)).2 =
    (408948561911567/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 833).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 833).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 833).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 833

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 833).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 833).criticalRate j.val*(generalMeanRows 833).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 833).c*(generalMeanRows 833).criticalPoint j.val)).2-
      (generalMeanRows 833).J/2-(generalMeanRows 833).error (generalMeanGrid j.val)+
      (generalMeanRows 833).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 833).c)).2-
      (generalMeanRows 833).J/2-(generalMeanRows 833).error 4 := by
  have he : (generalMeanRows 833).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 833) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 833)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0833

/-! Kernel-checked entropy margins for general spectral rectangle 834. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0834
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5015491118, 4842290024, 4676753743, 4518451811, 4366983927, 4221977323, 4083084415, 3949980701, 3822362878, 3699947148, 3582467686, 3469675259, 3361335970, 3257230125, 3157151189, 3060904848, 2968308141, 2879188671, 2793383880, 2710740383, 2631113358, 2554365978, 2480368896, 2408999759, 2340142768, 2273688268, 2209532362, 2147576560, 2087727453, 2029896403, 1973999263, 1919956109, 1867690997, 1817131729, 1768209642, 1720859403, 1675018825, 1630628690, 1587632582, 1545976737, 1505609897, 1466483172, 1428549916, 1391765605, 1356087728, 1321475678, 1287890651, 1255295561, 1223654941, 1192934869, 1163102884, 1134127915, 1105980212, 1078631278, 1052053810, 1026221637, 1001109669, 976693841, 952951066, 929859186, 907396933, 885543880, 864280405, 843587657, 823447514, 803842552, 784756017, 766171787, 748074350, 730448775, 713280684, 696556229, 680262069, 664385350, 648913677, 633835103, 619138104, 604811561, 590844747, 577227306, 563949242, 551000899, 538372951, 526056388, 514042500, 502322870, 490889357, 479734089, 468849451, 458228075, 447862828, 437746807, 427873329, 418235920, 408828309, 399644422, 390678371, 381924450, 373377127, 365031037, 356880977, 348921902, 341148915, 333557264, 326142338, 318899659, 311824882, 304913786, 298162269, 291566351, 285122161, 278825940, 272674032, 266662886, 260789048, 255049161, 249439957, 243958262, 238600985, 233365120, 228247742]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 834).prefactor = (74660140589759/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 834).cutoff/(generalMeanRows 834).c)).2 =
    (8795516839201/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 834).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 834).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 834).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 834

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 834).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 834).criticalRate j.val*(generalMeanRows 834).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 834).c*(generalMeanRows 834).criticalPoint j.val)).2-
      (generalMeanRows 834).J/2-(generalMeanRows 834).error (generalMeanGrid j.val)+
      (generalMeanRows 834).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 834).c)).2-
      (generalMeanRows 834).J/2-(generalMeanRows 834).error 4 := by
  have he : (generalMeanRows 834).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 834) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 834)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0834

/-! Kernel-checked entropy margins for general spectral rectangle 835. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0835
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5107823365, 4939681722, 4778884955, 4625018576, 4477697305, 4336562519, 4201279979, 4071537786, 3947044558, 3827527782, 3712732332, 3602419126, 3496363908, 3394356146, 3296198023, 3201703524, 3110697592, 3023015367, 2938501478, 2857009397, 2778400851, 2702545267, 2629319274, 2558606232, 2490295807, 2424283566, 2360470614, 2298763248, 2239072637, 2181314532, 2125408987, 2071280102, 2018855789, 1968067543, 1918850242, 1871141946, 1824883720, 1780019461, 1736495745, 1694261670, 1653268724, 1613470651, 1574823330, 1537284656, 1500814437, 1465374292, 1430927549, 1397439166, 1364875635, 1333204911, 1302396334, 1272420559, 1243249487, 1214856205, 1187214926, 1160300935, 1134090532, 1108560984, 1083690481, 1059458088, 1035843703, 1012828019, 990392485, 968519272, 947191238, 926391896, 906105383, 886316434, 867010353, 848172987, 829790703, 811850363, 794339303, 777245313, 760556615, 744261848, 728350045, 712810620, 697633350, 682808361, 668326111, 654177379, 640353250, 626845104, 613644601, 600743673, 588134511, 575809556, 563761488, 551983217, 540467874, 529208803, 518199553, 507433867, 496905681, 486609109, 476538443, 466688144, 457052834, 447627292, 438406450, 429385382, 420559305, 411923572, 403473665, 395205192, 387113885, 379195593, 371446276, 363862007, 356438964, 349173427, 342061777, 335100489, 328286133, 321615367, 315084936, 308691672, 302432484, 296304366, 290304383]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 835).prefactor = (1158215760215327/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 835).cutoff/(generalMeanRows 835).c)).2 =
    (76351794101519/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 835).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 835).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 835).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 835

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 835).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 835).criticalRate j.val*(generalMeanRows 835).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 835).c*(generalMeanRows 835).criticalPoint j.val)).2-
      (generalMeanRows 835).J/2-(generalMeanRows 835).error (generalMeanGrid j.val)+
      (generalMeanRows 835).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 835).c)).2-
      (generalMeanRows 835).J/2-(generalMeanRows 835).error 4 := by
  have he : (generalMeanRows 835).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 835) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 835)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0835

/-! Kernel-checked entropy margins for general spectral rectangle 836. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0836
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5227673875, 5057974684, 4895660765, 4740314994, 4591549675, 4449003963, 4312341574, 4181248729, 4055432313, 3934618218, 3818549845, 3706986755, 3599703441, 3496488214, 3397142192, 3301478371, 3209320787, 3120503737, 3034871073, 2952275552, 2872578235, 2795647938, 2721360722, 2649599425, 2580253228, 2513217254, 2448392192, 2385683959, 2325003373, 2266265857, 2209391165, 2154303120, 2100929377, 2049201195, 1999053232, 1950423347, 1903252417, 1857484169, 1813065016, 1769943912, 1728072208, 1687403523, 1647893617, 1609500280, 1572183219, 1535903960, 1500625746, 1466313454, 1432933503, 1400453779, 1368843557, 1338073431, 1308115246, 1278942036, 1250527965, 1222848269, 1195879203, 1169597995, 1143982791, 1119012618, 1094667338, 1070927608, 1047774843, 1025191180, 1003159443, 981663114, 960686300, 940213704, 920230600, 900722805, 881676655, 863078984, 844917098, 827178757, 809852154, 792925897, 776388989, 760230815, 744441120, 729010001, 713927885, 699185518, 684773956, 670684544, 656908912, 643438958, 630266841, 617384968, 604785985, 592462767, 580408412, 568616227, 557079726, 545792618, 534748800, 523942352, 513367528, 503018750, 492890604, 482977831, 473275323, 463778117, 454481391, 445380457, 436470759, 427747865, 419207466, 410845371, 402657499, 394639883, 386788660, 379100069, 371570448, 364196232, 356973948, 349900213, 342971731, 336185290, 329537759, 323026087, 316647299]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 836).prefactor = (58313174170479/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 836).cutoff/(generalMeanRows 836).c)).2 =
    (388953246141621/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 836).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 836).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 836).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 836

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 836).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 836).criticalRate j.val*(generalMeanRows 836).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 836).c*(generalMeanRows 836).criticalPoint j.val)).2-
      (generalMeanRows 836).J/2-(generalMeanRows 836).error (generalMeanGrid j.val)+
      (generalMeanRows 836).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 836).c)).2-
      (generalMeanRows 836).J/2-(generalMeanRows 836).error 4 := by
  have he : (generalMeanRows 836).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 836) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 836)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0836

/-! Kernel-checked entropy margins for general spectral rectangle 837. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0837
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5215038188, 5043367199, 4879195258, 4722099174, 4571685583, 4427588334, 4289466171, 4157000648, 4029894268, 3907868797, 3790663755, 3678035039, 3569753689, 3465604751, 3365386259, 3268908290, 3175992116, 3086469413, 3000181550, 2916978925, 2836720361, 2759272545, 2684509514, 2612312184, 2542567901, 2475170043, 2410017637, 2347015013, 2286071478, 2227101012, 2170021992, 2114756925, 2061232208, 2009377902, 1959127514, 1910417806, 1863188605, 1817382631, 1772945338, 1729824756, 1687971356, 1647337909, 1607879368, 1569552745, 1532317006, 1496132960, 1460963170, 1426771854, 1393524805, 1361189302, 1329734044, 1299129068, 1269345685, 1240356419, 1212134942, 1184656018, 1157895449, 1131830029, 1106437486, 1081696447, 1057586389, 1034087598, 1011181136, 988848797, 967073081, 945837154, 925124821, 904920496, 885209174, 865976406, 847208271, 828891358, 811012735, 793559937, 776520939, 759884139, 743638342, 727772740, 712276894, 697140724, 682354487, 667908768, 653794467, 640002780, 626525195, 613353472, 600479640, 587895980, 575595020, 563569519, 551812465, 540317063, 529076725, 518085064, 507335887, 496823187, 486541136, 476484075, 466646517, 457023130, 447608739, 438398316, 429386977, 420569977, 411942704, 403500674, 395239528, 387155028, 379243050, 371499585, 363920730, 356502687, 349241762, 342134354, 335176963, 328366175, 321698668, 315171207, 308780638, 302523888, 296397963]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 837).prefactor = (1182527074258081/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 837).cutoff/(generalMeanRows 837).c)).2 =
    (76351794101519/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 837).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 837).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 837).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 837

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 837).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 837).criticalRate j.val*(generalMeanRows 837).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 837).c*(generalMeanRows 837).criticalPoint j.val)).2-
      (generalMeanRows 837).J/2-(generalMeanRows 837).error (generalMeanGrid j.val)+
      (generalMeanRows 837).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 837).c)).2-
      (generalMeanRows 837).J/2-(generalMeanRows 837).error 4 := by
  have he : (generalMeanRows 837).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 837) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 837)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0837

/-! Kernel-checked entropy margins for general spectral rectangle 838. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0838
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5646079593, 5463855885, 5289563034, 5122753355, 4963010701, 4809947702, 4663203313, 4522440611, 4387344824, 4257621552, 4132995171, 4013207382, 3898015897, 3787193252, 3680525717, 3577812306, 3478863880, 3383502309, 3291559723, 3202877806, 3117307162, 3034706723, 2954943202, 2877890594, 2803429707, 2731447735, 2661837860, 2594498877, 2529334856, 2466254819, 2405172446, 2346005795, 2288677045, 2233112259, 2179241154, 2126996895, 2076315896, 2027137641, 1979404507, 1933061606, 1888056635, 1844339733, 1801863347, 1760582112, 1720452728, 1681433855, 1643486007, 1606571456, 1570654139, 1535699573, 1501674773, 1468548176, 1436289569, 1404870022, 1374261818, 1344438403, 1315374316, 1287045148, 1259427480, 1232498842, 1206237662, 1180623227, 1155635642, 1131255788, 1107465289, 1084246473, 1061582346, 1039456555, 1017853359, 996757605, 976154698, 956030578, 936371692, 917164978, 898397839, 880058122, 862134102, 844614462, 827488273, 810744983, 794374395, 778366656, 762712242, 747401943, 732426853, 717778351, 703448100, 689428025, 675710308, 662287379, 649151902, 636296768, 623715087, 611400179, 599345564, 587544959, 575992263, 564681560, 553607104, 542763316, 532144778, 521746227, 511562548, 501588772, 491820068, 482251737, 472879212, 463698049, 454703925, 445892634, 437260082, 428802283, 420515357, 412395526, 404439108, 396642519, 389002266, 381514944, 374177235, 366985906, 359937802]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 838).prefactor = (4951542943138281/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 838).cutoff/(generalMeanRows 838).c)).2 =
    (389632333991831/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 838).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 838).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 838).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 838

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 838).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 838).criticalRate j.val*(generalMeanRows 838).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 838).c*(generalMeanRows 838).criticalPoint j.val)).2-
      (generalMeanRows 838).J/2-(generalMeanRows 838).error (generalMeanGrid j.val)+
      (generalMeanRows 838).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 838).c)).2-
      (generalMeanRows 838).J/2-(generalMeanRows 838).error 4 := by
  have he : (generalMeanRows 838).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 838) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 838)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0838

/-! Kernel-checked entropy margins for general spectral rectangle 839. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0839
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4917501389, 4745234506, 4580675834, 4423388994, 4272968309, 4129036122, 3991240409, 3859252637, 3732765852, 3611492945, 3495165099, 3383530374, 3276352436, 3173409391, 3074492729, 2979406363, 2887965745, 2799997061, 2715336490, 2633829529, 2555330365, 2479701298, 2406812217, 2336540105, 2268768587, 2203387513, 2140292565, 2079384901, 2020570821, 1963761449, 1908872453, 1855823769, 1804539350, 1754946937, 1706977836, 1660566712, 1615651405, 1572172744, 1530074386, 1489302654, 1449806394, 1411536837, 1374447469, 1338493908, 1303633795, 1269826683, 1237033936, 1205218638, 1174345502, 1144380784, 1115292207, 1087048888, 1059621260, 1032981017, 1007101042, 981955353, 957519045, 933768241, 910680037, 888232460, 866404419, 845175669, 824526764, 804439026, 784894504, 765875943, 747366753, 729350977, 711813262, 694738831, 678113461, 661923455, 646155619, 630797242, 615836071, 601260297, 587058529, 573219782, 559733458, 546589327, 533777515, 521288487, 509113035, 497242263, 485667574, 474380660, 463373489, 452638292, 442167556, 431954014, 421990630, 412270598, 402787325, 393534432, 384505735, 375695247, 367097166, 358705870, 350515907, 342521993, 334719004, 327101969, 319666068, 312406622, 305319092, 298399070, 291642281, 285044569, 278601902, 272310362, 266166144, 260165550, 254304988, 248580965, 242990087, 237529055, 232194660, 226983781, 221893385, 216920520, 212062314]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 839).prefactor = (1205359285891651/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 839).cutoff/(generalMeanRows 839).c)).2 =
    (355742627920543/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 839).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 839).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 839).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 839

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 839).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 839).criticalRate j.val*(generalMeanRows 839).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 839).c*(generalMeanRows 839).criticalPoint j.val)).2-
      (generalMeanRows 839).J/2-(generalMeanRows 839).error (generalMeanGrid j.val)+
      (generalMeanRows 839).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 839).c)).2-
      (generalMeanRows 839).J/2-(generalMeanRows 839).error 4 := by
  have he : (generalMeanRows 839).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 839) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 839)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0839

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock11 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 11 i) := by
  fin_cases i
  · exact EntropyRow0770.numerical
  · exact EntropyRow0771.numerical
  · exact EntropyRow0772.numerical
  · exact EntropyRow0773.numerical
  · exact EntropyRow0774.numerical
  · exact EntropyRow0775.numerical
  · exact EntropyRow0776.numerical
  · exact EntropyRow0777.numerical
  · exact EntropyRow0778.numerical
  · exact EntropyRow0779.numerical
  · exact EntropyRow0780.numerical
  · exact EntropyRow0781.numerical
  · exact EntropyRow0782.numerical
  · exact EntropyRow0783.numerical
  · exact EntropyRow0784.numerical
  · exact EntropyRow0785.numerical
  · exact EntropyRow0786.numerical
  · exact EntropyRow0787.numerical
  · exact EntropyRow0788.numerical
  · exact EntropyRow0789.numerical
  · exact EntropyRow0790.numerical
  · exact EntropyRow0791.numerical
  · exact EntropyRow0792.numerical
  · exact EntropyRow0793.numerical
  · exact EntropyRow0794.numerical
  · exact EntropyRow0795.numerical
  · exact EntropyRow0796.numerical
  · exact EntropyRow0797.numerical
  · exact EntropyRow0798.numerical
  · exact EntropyRow0799.numerical
  · exact EntropyRow0800.numerical
  · exact EntropyRow0801.numerical
  · exact EntropyRow0802.numerical
  · exact EntropyRow0803.numerical
  · exact EntropyRow0804.numerical
  · exact EntropyRow0805.numerical
  · exact EntropyRow0806.numerical
  · exact EntropyRow0807.numerical
  · exact EntropyRow0808.numerical
  · exact EntropyRow0809.numerical
  · exact EntropyRow0810.numerical
  · exact EntropyRow0811.numerical
  · exact EntropyRow0812.numerical
  · exact EntropyRow0813.numerical
  · exact EntropyRow0814.numerical
  · exact EntropyRow0815.numerical
  · exact EntropyRow0816.numerical
  · exact EntropyRow0817.numerical
  · exact EntropyRow0818.numerical
  · exact EntropyRow0819.numerical
  · exact EntropyRow0820.numerical
  · exact EntropyRow0821.numerical
  · exact EntropyRow0822.numerical
  · exact EntropyRow0823.numerical
  · exact EntropyRow0824.numerical
  · exact EntropyRow0825.numerical
  · exact EntropyRow0826.numerical
  · exact EntropyRow0827.numerical
  · exact EntropyRow0828.numerical
  · exact EntropyRow0829.numerical
  · exact EntropyRow0830.numerical
  · exact EntropyRow0831.numerical
  · exact EntropyRow0832.numerical
  · exact EntropyRow0833.numerical
  · exact EntropyRow0834.numerical
  · exact EntropyRow0835.numerical
  · exact EntropyRow0836.numerical
  · exact EntropyRow0837.numerical
  · exact EntropyRow0838.numerical
  · exact EntropyRow0839.numerical
end SingularValueBounds.KL.Certificates
