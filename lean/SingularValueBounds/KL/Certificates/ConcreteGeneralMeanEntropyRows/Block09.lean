import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 630. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0630
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5359332376, 5182618691, 5013738022, 4852242714, 4697716816, 4549773309, 4408051637, 4272215499, 4141950858, 4016964163, 3896980732, 3781743294, 3671010670, 3564556571, 3462168503, 3363646773, 3268803572, 3177462146, 3089456028, 3004628338, 2922831130, 2843924806, 2767777560, 2694264875, 2623269052, 2554678776, 2488388717, 2424299156, 2362315636, 2302348645, 2244313311, 2188129131, 2133719705, 2081012495, 2029938605, 1980432561, 1932432120, 1885878086, 1840714133, 1796886648, 1754344578, 1713039288, 1672924428, 1633955809, 1596091286, 1559290646, 1523515506, 1488729218, 1454896772, 1421984717, 1389961072, 1358795258, 1328458018, 1298921357, 1270158474, 1242143698, 1214852441, 1188261136, 1162347188, 1137088929, 1112465571, 1088457161, 1065044545, 1042209328, 1019933835, 998201081, 976994738, 956299100, 936099060, 916380080, 897128162, 878329827, 859972093, 842042447, 824528829, 807419609, 790703571, 774369892, 758408127, 742808190, 727560343, 712655177, 698083600, 683836823, 669906350, 656283961, 642961706, 629931889, 617187063, 604720013, 592523757, 580591525, 568916760, 557493104, 546314395, 535374655, 524668086, 514189061, 503932120, 493891962, 484063440, 474441555, 465021451, 455798410, 446767845, 437925300, 429266438, 420787047, 412483024, 404350383, 396385241, 388583820, 380942444, 373457532, 366125597, 358943244, 351907164, 345014135, 338261015, 331644744, 325162337]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 630).prefactor = (2430252768373213/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 630).cutoff/(generalMeanRows 630).c)).2 =
    (395656324032343/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 630).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 630).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 630).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 630

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 630).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 630).criticalRate j.val*(generalMeanRows 630).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 630).c*(generalMeanRows 630).criticalPoint j.val)).2-
      (generalMeanRows 630).J/2-(generalMeanRows 630).error (generalMeanGrid j.val)+
      (generalMeanRows 630).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 630).c)).2-
      (generalMeanRows 630).J/2-(generalMeanRows 630).error 4 := by
  have he : (generalMeanRows 630).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 630) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 630)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0630

/-! Kernel-checked entropy margins for general spectral rectangle 631. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0631
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5581926282, 5403257658, 5232455186, 5069068359, 4912678632, 4762896635, 4619359676, 4481729515, 4349690360, 4222947066, 4101223511, 3984261121, 3871817540, 3763665418, 3659591306, 3559394652, 3462886880, 3369890550, 3280238583, 3193773556, 3110347045, 3029819029, 2952057335, 2876937125, 2804340426, 2734155689, 2666277386, 2600605635, 2537045847, 2475508406, 2415908362, 2358165157, 2302202357, 2247947410, 2195331421, 2144288936, 2094757743, 2046678690, 1999995508, 1954654647, 1910605129, 1867798400, 1826188198, 1785730427, 1746383040, 1708105926, 1670860809, 1634611146, 1599322040, 1564960148, 1531493604, 1498891940, 1467126012, 1436167937, 1405991025, 1376569716, 1347879530, 1319897008, 1292599659, 1265965920, 1239975102, 1214607353, 1189843612, 1165665579, 1142055668, 1118996982, 1096473275, 1074468925, 1052968901, 1031958739, 1011424512, 991352812, 971730717, 952545778, 933785992, 915439783, 897495987, 879943827, 862772904, 845973172, 829534931, 813448807, 797705739, 782296966, 767214017, 752448695, 737993068, 723839457, 709980426, 696408774, 683117523, 670099910, 657349378, 644859571, 632624322, 620637647, 608893741, 597386967, 586111851, 575063077, 564235482, 553624047, 543223895, 533030283, 523038601, 513244363, 503643205, 494230883, 485003263, 475956322, 467086143, 458388910, 449860909, 441498517, 433298207, 425256540, 417370163, 409635808, 402050287, 394610491, 387313387]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 631).prefactor = (4894142075007219/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 631).cutoff/(generalMeanRows 631).c)).2 =
    (41098229451057/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 631).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 631).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 631).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 631

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 631).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 631).criticalRate j.val*(generalMeanRows 631).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 631).c*(generalMeanRows 631).criticalPoint j.val)).2-
      (generalMeanRows 631).J/2-(generalMeanRows 631).error (generalMeanGrid j.val)+
      (generalMeanRows 631).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 631).c)).2-
      (generalMeanRows 631).J/2-(generalMeanRows 631).error 4 := by
  have he : (generalMeanRows 631).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 631) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 631)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0631

/-! Kernel-checked entropy margins for general spectral rectangle 632. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0632
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5177912125, 4999912467, 4829862928, 4667312210, 4511840802, 4363058203, 4220600453, 4084127915, 3953323288, 3827889823, 3707549706, 3592042598, 3481124316, 3374565629, 3272151163, 3173678406, 3078956794, 2987806875, 2900059545, 2815555347, 2734143819, 2655682904, 2580038396, 2507083437, 2436698044, 2368768676, 2303187832, 2239853679, 2178669701, 2119544382, 2062390901, 2007126858, 1953674009, 1901958024, 1851908265, 1803457568, 1756542049, 1711100917, 1667076304, 1624413096, 1583058788, 1542963337, 1504079032, 1466360361, 1429763903, 1394248208, 1359773698, 1326302567, 1293798690, 1262227532, 1231556074, 1201752726, 1172787262, 1144630749, 1117255480, 1090634915, 1064743625, 1039557233, 1015052367, 991206608, 967998446, 945407237, 923413160, 901997176, 881141000, 860827053, 841038442, 821758918, 802972854, 784665211, 766821517, 749427835, 732470746, 715937320, 699815100, 684092075, 668756666, 653797705, 639204419, 624966409, 611073638, 597516417, 584285386, 571371502, 558766029, 546460520, 534446811, 522717005, 511263463, 500078794, 489155846, 478487694, 468067633, 457889171, 447946016, 438232074, 428741437, 419468379, 410407347, 401552958, 392899987, 384443367, 376178180, 368099652, 360203150, 352484174, 344938354, 337561445, 330349322, 323297978, 316403518, 309662155, 303070209, 296624099, 290320344, 284155558, 278126445, 272229800, 266462503, 260821517, 255303886]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 632).prefactor = (2451860097971279/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 632).cutoff/(generalMeanRows 632).c)).2 =
    (367400955493631/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 632).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 632).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 632).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 632

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 632).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 632).criticalRate j.val*(generalMeanRows 632).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 632).c*(generalMeanRows 632).criticalPoint j.val)).2-
      (generalMeanRows 632).J/2-(generalMeanRows 632).error (generalMeanGrid j.val)+
      (generalMeanRows 632).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 632).c)).2-
      (generalMeanRows 632).J/2-(generalMeanRows 632).error 4 := by
  have he : (generalMeanRows 632).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 632) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 632)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0632

/-! Kernel-checked entropy margins for general spectral rectangle 633. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0633
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5301172010, 5121420713, 4949666610, 4785455456, 4628365028, 4478002331, 4334001106, 4196019597, 4063738550, 3936859409, 3815102693, 3698206523, 3585925291, 3478028445, 3374299394, 3274534495, 3178542134, 3086141893, 2997163769, 2911447469, 2828841761, 2749203869, 2672398924, 2598299449, 2526784888, 2457741170, 2391060298, 2326639981, 2264383277, 2204198274, 2145997782, 2089699057, 2035223538, 1982496600, 1931447325, 1882008295, 1834115384, 1787707580, 1742726803, 1699117747, 1656827724, 1615806522, 1576006268, 1537381304, 1499888066, 1463484973, 1428132324, 1393792197, 1360428355, 1328006162, 1296492497, 1265855679, 1236065394, 1207092623, 1178909579, 1151489647, 1124807321, 1098838155, 1073558709, 1048946497, 1024979948, 1001638354, 978901834, 956751293, 935168386, 914135481, 893635628, 873652526, 854170494, 835174443, 816649846, 798582719, 780959590, 763767480, 746993881, 730626733, 714654409, 699065690, 683849755, 668996155, 654494806, 640335967, 626510231, 613008507, 599822007, 586942237, 574360982, 562070296, 550062491, 538330127, 526866000, 515663137, 504714782, 494014393, 483555627, 473332339, 463338572, 453568549, 444016665, 434677486, 425545737, 416616299, 407884202, 399344623, 390992875, 382824407, 374834798, 367019751, 359375091, 351896757, 344580804, 337423393, 330420791, 323569368, 316865590, 310306019, 303887308, 297606202, 291459528, 285444198, 279557206]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 633).prefactor = (493822352565499/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 633).cutoff/(generalMeanRows 633).c)).2 =
    (18743183834761/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 633).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 633).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 633).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 633

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 633).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 633).criticalRate j.val*(generalMeanRows 633).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 633).c*(generalMeanRows 633).criticalPoint j.val)).2-
      (generalMeanRows 633).J/2-(generalMeanRows 633).error (generalMeanGrid j.val)+
      (generalMeanRows 633).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 633).c)).2-
      (generalMeanRows 633).J/2-(generalMeanRows 633).error 4 := by
  have he : (generalMeanRows 633).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 633) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 633)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0633

/-! Kernel-checked entropy margins for general spectral rectangle 634. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0634
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5419838852, 5233811606, 5056084845, 4886188149, 4723684189, 4568165837, 4419253590, 4276593268, 4139853946, 4008726092, 3882919887, 3762163714, 3646202774, 3534797841, 3427724121, 3324770217, 3225737177, 3130437628, 3038694980, 2950342693, 2865223606, 2783189315, 2704099605, 2627821918, 2554230870, 2483207794, 2414640323, 2348422005, 2284451934, 2222634424, 2162878690, 2105098559, 2049212202, 1995141874, 1942813688, 1892157384, 1843106131, 1795596329, 1749567432, 1704961774, 1661724416, 1619802993, 1579147578, 1539710546, 1501446455, 1464311929, 1428265549, 1393267749, 1359280725, 1326268335, 1294196023, 1263030732, 1232740832, 1203296043, 1174667375, 1146827057, 1119748481, 1093406142, 1067775587, 1042833363, 1018556968, 994924805, 971916143, 949511072, 927690463, 906435939, 885729832, 865555154, 845895566, 826735348, 808059372, 789853072, 772102422, 754793914, 737914528, 721451719, 705393390, 689727876, 674443923, 659530674, 644977650, 630774731, 616912148, 603380462, 590170554, 577273610, 564681110, 552384815, 540376756, 528649224, 517194757, 506006136, 495076367, 484398682, 473966521, 463773531, 453813554, 444080622, 434568949, 425272924, 416187104, 407306209, 398625117, 390138855, 381842595, 373731653, 365801476, 358047643, 350465862, 343051958, 335801876, 328711674, 321777521, 314995690, 308362556, 301874595, 295528377, 289320566, 283247914, 277307261, 271495531]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 634).prefactor = (2544003915023839/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 634).cutoff/(generalMeanRows 634).c)).2 =
    (182803837185913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 634).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 634).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 634).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 634

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 634).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 634).criticalRate j.val*(generalMeanRows 634).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 634).c*(generalMeanRows 634).criticalPoint j.val)).2-
      (generalMeanRows 634).J/2-(generalMeanRows 634).error (generalMeanGrid j.val)+
      (generalMeanRows 634).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 634).c)).2-
      (generalMeanRows 634).J/2-(generalMeanRows 634).error 4 := by
  have he : (generalMeanRows 634).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 634) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 634)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0634

/-! Kernel-checked entropy margins for general spectral rectangle 635. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0635
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5643207003, 5454852742, 5274839873, 5102695004, 4937978098, 4780279569, 4629217677, 4484436206, 4345602380, 4212404986, 4084552679, 3961772451, 3843808245, 3730419693, 3621380967, 3516479735, 3415516199, 3318302224, 3224660533, 3134423969, 3047434818, 2963544181, 2882611402, 2804503529, 2729094831, 2656266334, 2585905402, 2517905346, 2452165058, 2388588674, 2327085261, 2267568518, 2209956509, 2154171407, 2100139251, 2047789731, 1997055976, 1947874358, 1900184315, 1853928177, 1809051007, 1765500452, 1723226599, 1682181849, 1642320787, 1603600069, 1565978313, 1529415991, 1493875339, 1459320260, 1425716239, 1393030265, 1361230752, 1330287467, 1300171462, 1270855011, 1242311547, 1214515609, 1187442783, 1161069655, 1135373758, 1110333532, 1085928277, 1062138112, 1038943940, 1016327405, 994270864, 972757349, 951770538, 931294728, 911314800, 891816200, 872784909, 854207420, 836070717, 818362251, 801069923, 784182059, 767687398, 751575068, 735834574, 720455782, 705428900, 690744468, 676393340, 662366676, 648655924, 635252815, 622149345, 609337766, 596810581, 584560526, 572580566, 560863888, 549403884, 538194153, 527228487, 516500865, 506005447, 495736565, 485688721, 475856576, 466234947, 456818798, 447603242, 438583527, 429755037, 421113285, 412653908, 404372666, 396265432, 388328195, 380557051, 372948201, 365497947, 358202691, 351058928, 344063248, 337212325, 330502925, 323931892]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 635).prefactor = (2562237398948987/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 635).cutoff/(generalMeanRows 635).c)).2 =
    (95204273258839/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 635).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 635).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 635).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 635

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 635).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 635).criticalRate j.val*(generalMeanRows 635).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 635).c*(generalMeanRows 635).criticalPoint j.val)).2-
      (generalMeanRows 635).J/2-(generalMeanRows 635).error (generalMeanGrid j.val)+
      (generalMeanRows 635).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 635).c)).2-
      (generalMeanRows 635).J/2-(generalMeanRows 635).error 4 := by
  have he : (generalMeanRows 635).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 635) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 635)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0635

/-! Kernel-checked entropy margins for general spectral rectangle 636. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0636
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5519181576, 5337263511, 5163379478, 4997072414, 4837917538, 4685519533, 4539510031, 4399545362, 4265304533, 4136487413, 4012813093, 3894018399, 3779856553, 3670095947, 3564519034, 3462921308, 3365110387, 3270905154, 3180134986, 3092639034, 3008265572, 2926871385, 2848321217, 2772487249, 2699248627, 2628491019, 2560106207, 2493991707, 2430050414, 2368190281, 2308324008, 2250368763, 2194245914, 2139880785, 2087202426, 2036143395, 1986639563, 1938629919, 1892056400, 1846863723, 1802999232, 1760412753, 1719056458, 1678884739, 1639854086, 1601922976, 1565051769, 1529202605, 1494339312, 1460427320, 1427433576, 1395326464, 1364075737, 1333652442, 1304028859, 1275178436, 1247075732, 1219696361, 1193016943, 1167015051, 1141669167, 1116958638, 1092863634, 1069365108, 1046444761, 1024085004, 1002268926, 980980265, 960203373, 939923192, 920125226, 900795513, 881920607, 863487546, 845483839, 827897440, 810716732, 793930506, 777527941, 761498594, 745832379, 730519551, 715550697, 700916714, 686608806, 672618463, 658937452, 645557810, 632471824, 619672031, 607151201, 594902331, 582918635, 571193536, 559720657, 548493816, 537507016, 526754438, 516230435, 505929527, 495846393, 485975867, 476312927, 466852700, 457590446, 448521560, 439641564, 430946105, 422430949, 414091977, 405925182, 397926664, 390092628, 382419378, 374903318, 367540943, 360328840, 353263687, 346342242, 339561351, 332917935]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 636).prefactor = (621621203262931/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 636).cutoff/(generalMeanRows 636).c)).2 =
    (48744787864713/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 636).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 636).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 636).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 636

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 636).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 636).criticalRate j.val*(generalMeanRows 636).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 636).c*(generalMeanRows 636).criticalPoint j.val)).2-
      (generalMeanRows 636).J/2-(generalMeanRows 636).error (generalMeanGrid j.val)+
      (generalMeanRows 636).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 636).c)).2-
      (generalMeanRows 636).J/2-(generalMeanRows 636).error 4 := by
  have he : (generalMeanRows 636).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 636) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 636)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0636

/-! Kernel-checked entropy margins for general spectral rectangle 637. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0637
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5748148433, 5564192800, 5388306224, 5220028689, 5058932736, 4904620611, 4756721734, 4614890424, 4478803866, 4348160275, 4222677240, 4102090231, 3986151241, 3874627552, 3767300617, 3663965031, 3564427603, 3468506491, 3376030425, 3286837982, 3200776923, 3117703583, 3037482309, 2959984936, 2885090311, 2812683843, 2742657094, 2674907396, 2609337493, 2545855214, 2484373163, 2424808437, 2367082353, 2311120207, 2256851035, 2204207402, 2153125195, 2103543438, 2055404109, 2008651982, 1963234462, 1919101448, 1876205191, 1834500165, 1793942951, 1754492122, 1716108132, 1678753224, 1642391328, 1606987979, 1572510229, 1538926571, 1506206862, 1474322258, 1443245143, 1412949072, 1383408707, 1354599765, 1326498967, 1299083986, 1272333399, 1246226650, 1220743998, 1195866488, 1171575906, 1147854748, 1124686184, 1102054028, 1079942709, 1058337239, 1037223191, 1016586668, 996414285, 976693140, 957410796, 938555260, 920114962, 902078738, 884435812, 867175778, 850288584, 833764520, 817594200, 801768549, 786278792, 771116439, 756273277, 741741353, 727512968, 713580665, 699937222, 686575636, 673489123, 660671103, 648115194, 635815206, 623765132, 611959141, 600391572, 589056927, 577949866, 567065200, 556397888, 545943028, 535695853, 525651730, 515806151, 506154728, 496693193, 487417391, 478323277, 469406913, 460664462, 452092186, 443686445, 435443689, 427360461, 419433388, 411659182, 404034638, 396556627]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 637).prefactor = (5007960205460177/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 637).cutoff/(generalMeanRows 637).c)).2 =
    (405284273395933/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 637).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 637).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 637).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 637

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 637).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 637).criticalRate j.val*(generalMeanRows 637).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 637).c*(generalMeanRows 637).criticalPoint j.val)).2-
      (generalMeanRows 637).J/2-(generalMeanRows 637).error (generalMeanGrid j.val)+
      (generalMeanRows 637).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 637).c)).2-
      (generalMeanRows 637).J/2-(generalMeanRows 637).error 4 := by
  have he : (generalMeanRows 637).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 637) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 637)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0637

/-! Kernel-checked entropy margins for general spectral rectangle 638. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0638
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5973447966, 5780250440, 5595577086, 5418941570, 5249891942, 5088007628, 4932896758, 4784193763, 4641557230, 4504667962, 4373227235, 4246955217, 4125589537, 4008883984, 3896607322, 3788542211, 3684484219, 3584240918, 3487631055, 3394483794, 3304638011, 3217941651, 3134251136, 3053430811, 2975352439, 2899894731, 2826942907, 2756388296, 2688127958, 2622064334, 2558104925, 2496161987, 2436152247, 2377996645, 2321620088, 2266951216, 2213922194, 2162468506, 2112528772, 2064044571, 2016960274, 1971222893, 1926781935, 1883589265, 1841598981, 1800767290, 1761052399, 1722414409, 1684815212, 1648218400, 1612589175, 1577894266, 1544101853, 1511181488, 1479104031, 1447841578, 1417367405, 1387655905, 1358682534, 1330423760, 1302857009, 1275960625, 1249713821, 1224096637, 1199089903, 1174675201, 1150834827, 1127551762, 1104809634, 1082592695, 1060885786, 1039674314, 1018944225, 998681979, 978874529, 959509295, 940574148, 922057389, 903947726, 886234262, 868906475, 851954202, 835367624, 819137253, 803253914, 787708738, 772493143, 757598827, 743017753, 728742143, 714764460, 701077407, 687673912, 674547120, 661690385, 649097264, 636761504, 624677040, 612837986, 601238626, 589873413, 578736956, 567824019, 557129515, 546648499, 536376163, 526307834, 516438963, 506765128, 497282025, 487985466, 478871373, 469935775, 461174807, 452584703, 444161795, 435902507, 427803356, 419860945, 412071963, 404433183]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 638).prefactor = (2615140972932949/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 638).cutoff/(generalMeanRows 638).c)).2 =
    (401463484337487/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 638).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 638).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 638).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 638

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 638).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 638).criticalRate j.val*(generalMeanRows 638).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 638).c*(generalMeanRows 638).criticalPoint j.val)).2-
      (generalMeanRows 638).J/2-(generalMeanRows 638).error (generalMeanGrid j.val)+
      (generalMeanRows 638).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 638).c)).2-
      (generalMeanRows 638).J/2-(generalMeanRows 638).error 4 := by
  have he : (generalMeanRows 638).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 638) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 638)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0638

/-! Kernel-checked entropy margins for general spectral rectangle 639. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0639
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5139688504, 4970018736, 4807952398, 4653048191, 4504896392, 4363116089, 4227352724, 4097275883, 3972577312, 3852969135, 3738182243, 3627964835, 3522081094, 3420309988, 3322444174, 3228289000, 3137661594, 3050390025, 2966312542, 2885276868, 2807139553, 2731765381, 2659026819, 2588803511, 2520981810, 2455454346, 2392119622, 2330881645, 2271649578, 2214337425, 2158863727, 2105151287, 2053126915, 2002721184, 1953868206, 1906505427, 1860573426, 1816015737, 1772778678, 1730811189, 1690064686, 1650492919, 1612051841, 1574699489, 1538395862, 1503102822, 1468783984, 1435404626, 1402931598, 1371333240, 1340579298, 1310640855, 1281490258, 1253101055, 1225447928, 1198506641, 1172253979, 1146667700, 1121726484, 1097409888, 1073698304, 1050572912, 1028015648, 1006009164, 984536793, 963582518, 943130939, 923167246, 903677190, 884647055, 866063637, 847914218, 830186544, 812868805, 795949614, 779417987, 763263328, 747475410, 732044359, 716960638, 702215035, 687798647, 673702866, 659919369, 646440106, 633257285, 620363368, 607751053, 595413270, 583343171, 571534118, 559979678, 548673613, 537609875, 526782596, 516186081, 505814804, 495663401, 485726660, 475999523, 466477072, 457154530, 448027255, 439090731, 430340569, 421772500, 413382370, 405166138, 397119871, 389239740, 381522019, 373963077, 366559380, 359307484, 352204034, 345245761, 338429479, 331752080, 325210539, 318801900, 312523286]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 639).prefactor = (2394783830501389/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 639).cutoff/(generalMeanRows 639).c)).2 =
    (41504559546029/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 639).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 639).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 639).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 639

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 639).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 639).criticalRate j.val*(generalMeanRows 639).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 639).c*(generalMeanRows 639).criticalPoint j.val)).2-
      (generalMeanRows 639).J/2-(generalMeanRows 639).error (generalMeanGrid j.val)+
      (generalMeanRows 639).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 639).c)).2-
      (generalMeanRows 639).J/2-(generalMeanRows 639).error 4 := by
  have he : (generalMeanRows 639).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 639) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 639)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0639

/-! Kernel-checked entropy margins for general spectral rectangle 640. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0640
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5773860365, 5578867968, 5392534404, 5214369302, 5043916776, 4880752415, 4724480597, 4574732089, 4431161891, 4293447299, 4161286154, 4034395260, 3912508953, 3795377798, 3682767402, 3574457334, 3470240136, 3369920419, 3273314035, 3180247312, 3090556357, 3004086408, 2920691237, 2840232607, 2762579754, 2687608924, 2615202932, 2545250762, 2477647183, 2412292406, 2349091759, 2287955377, 2228797927, 2171538341, 2116099569, 2062408353, 2010395005, 1959993214, 1911139852, 1863774800, 1817840780, 1773283202, 1730050021, 1688091592, 1647360549, 1607811683, 1569401825, 1532089741, 1495836033, 1460603042, 1426354758, 1393056739, 1360676030, 1329181085, 1298541703, 1268728956, 1239715126, 1211473650, 1183979058, 1157206924, 1131133815, 1105737240, 1080995611, 1056888196, 1033395079, 1010497123, 988175934, 966413825, 945193786, 924499451, 904315068, 884625476, 865416073, 846672793, 828382085, 810530886, 793106604, 776097092, 759490636, 743275929, 727442059, 711978491, 696875050, 682121907, 667709563, 653628839, 639870858, 626427038, 613289075, 600448936, 587898845, 575631276, 563638940, 551914778, 540451951, 529243832, 518283999, 507566223, 497084467, 486832873, 476805759, 466997613, 457403082, 448016971, 438834237, 429849980, 421059442, 412457998, 404041157, 395804550, 387743933, 379855177, 372134268, 364577301, 357180476, 349940097, 342852567, 335914384, 329122138, 322472511, 315962269]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 640).prefactor = (264082331723213/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 640).cutoff/(generalMeanRows 640).c)).2 =
    (4653265083109/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 640).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 640).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 640).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 640

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 640).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 640).criticalRate j.val*(generalMeanRows 640).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 640).c*(generalMeanRows 640).criticalPoint j.val)).2-
      (generalMeanRows 640).J/2-(generalMeanRows 640).error (generalMeanGrid j.val)+
      (generalMeanRows 640).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 640).c)).2-
      (generalMeanRows 640).J/2-(generalMeanRows 640).error 4 := by
  have he : (generalMeanRows 640).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 640) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 640)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0640

/-! Kernel-checked entropy margins for general spectral rectangle 641. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0641
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5043408703, 4872069101, 4708439442, 4552075055, 4402562927, 4259518938, 4122585397, 3991428829, 3865737990, 3745222082, 3629609140, 3518644572, 3412089833, 3309721228, 3211328811, 3116715388, 3025695608, 2938095118, 2853749807, 2772505093, 2694215284, 2618742975, 2545958503, 2475739438, 2407970113, 2342541194, 2279349274, 2218296501, 2159290236, 2102242726, 2047070811, 1993695641, 1942042420, 1892040166, 1843621482, 1796722350, 1751281933, 1707242391, 1664548710, 1623148545, 1582992065, 1544031813, 1506222578, 1469521267, 1433886793, 1399279962, 1365663372, 1333001320, 1301259709, 1270405961, 1240408941, 1211238881, 1182867307, 1155266975, 1128411807, 1102276830, 1076838123, 1052072764, 1027958779, 1004475094, 981601494, 959318580, 937607726, 916451048, 895831363, 875732158, 856137558, 837032298, 818401690, 800231603, 782508429, 765219067, 748350896, 731891755, 715829919, 700154086, 684853353, 669917199, 655335472, 641098370, 627196427, 613620498, 600361748, 587411634, 574761900, 562404559, 550331884, 538536399, 527010867, 515748281, 504741855, 493985017, 483471397, 473194822, 463149307, 453329050, 443728421, 434341962, 425164373, 416190513, 407415388, 398834151, 390442094, 382234644, 374207356, 366355913, 358676117, 351163887, 343815255, 336626361, 329593451, 322712873, 315981073, 309394592, 302950063, 296644207, 290473833, 284435833, 278527177, 272744918, 267086180]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 641).prefactor = (4830272054520123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 641).cutoff/(generalMeanRows 641).c)).2 =
    (394411728264091/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 641).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 641).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 641).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 641

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 641).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 641).criticalRate j.val*(generalMeanRows 641).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 641).c*(generalMeanRows 641).criticalPoint j.val)).2-
      (generalMeanRows 641).J/2-(generalMeanRows 641).error (generalMeanGrid j.val)+
      (generalMeanRows 641).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 641).c)).2-
      (generalMeanRows 641).J/2-(generalMeanRows 641).error 4 := by
  have he : (generalMeanRows 641).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 641) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 641)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0641

/-! Kernel-checked entropy margins for general spectral rectangle 642. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0642
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5172946094, 5002178437, 4839063410, 4683156858, 4534046407, 4391348681, 4254706827, 4123788292, 3998282828, 3877900698, 3762371050, 3651440453, 3544871566, 3442441926, 3343942847, 3249178420, 3157964587, 3070128307, 2985506781, 2903946746, 2825303825, 2749441926, 2676232691, 2605554987, 2537294429, 2471342954, 2407598407, 2345964175, 2286348833, 2228665828, 2172833174, 2118773175, 2066412167, 2015680273, 1966511180, 1918841928, 1872612713, 1827766703, 1784249868, 1742010819, 1701000656, 1661172830, 1622483010, 1584888960, 1548350423, 1512829010, 1478288104, 1444692757, 1412009605, 1380206781, 1349253838, 1319121671, 1289782449, 1261209546, 1233377484, 1206261867, 1179839330, 1154087489, 1128984885, 1104510943, 1080645927, 1057370896, 1034667670, 1012518788, 990907475, 969817610, 949233695, 929140822, 909524650, 890371376, 871667710, 853400851, 835558466, 818128668, 801099997, 784461398, 768202207, 752312129, 736781228, 721599904, 706758886, 692249213, 678062222, 664189536, 650623052, 637354929, 624377578, 611683652, 599266035, 587117833, 575232367, 563603161, 552223938, 541088609, 530191269, 519526187, 509087800, 498870710, 488869671, 479079592, 469495524, 460112659, 450926323, 441931973, 433125191, 424501681, 416057260, 407787863, 399689531, 391758410, 383990749, 376382895, 368931290, 361632469, 354483055, 347479757, 340619368, 333898762, 327314892, 320864785, 314545543]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 642).prefactor = (4820559709993833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 642).cutoff/(generalMeanRows 642).c)).2 =
    (41504559546029/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 642).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 642).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 642).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 642

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 642).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 642).criticalRate j.val*(generalMeanRows 642).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 642).c*(generalMeanRows 642).criticalPoint j.val)).2-
      (generalMeanRows 642).J/2-(generalMeanRows 642).error (generalMeanGrid j.val)+
      (generalMeanRows 642).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 642).c)).2-
      (generalMeanRows 642).J/2-(generalMeanRows 642).error 4 := by
  have he : (generalMeanRows 642).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 642) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 642)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0642

/-! Kernel-checked entropy margins for general spectral rectangle 643. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0643
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5206418885, 5034546235, 4870375733, 4713460351, 4563385044, 4419763958, 4282237930, 4150472255, 4024154678, 3902993587, 3786716376, 3675067977, 3567809510, 3464717074, 3365580634, 3270203010, 3178398956, 3089994310, 3004825220, 2922737431, 2843585632, 2767232851, 2693549898, 2622414857, 2553712603, 2487334373, 2423177351, 2361144300, 2301143203, 2243086946, 2186893013, 2132483206, 2079783383, 2028723217, 1979235964, 1931258256, 1884729904, 1839593707, 1795795286, 1753282919, 1712007390, 1671921848, 1632981677, 1595144365, 1558369396, 1522618134, 1487853722, 1454040988, 1421146352, 1389137741, 1357984509, 1327657365, 1298128296, 1269370506, 1241358349, 1214067274, 1187473764, 1161555289, 1136290253, 1111657946, 1087638506, 1064212869, 1041362736, 1019070534, 997319380, 976093048, 955375939, 935153051, 915409948, 896132738, 877308046, 858922986, 840965148, 823422567, 806283707, 789537444, 773173044, 757180146, 741548748, 726269190, 711332139, 696728578, 682449787, 668487334, 654833065, 641479087, 628417763, 615641698, 603143730, 590916920, 578954546, 567250090, 555797235, 544589853, 533621999, 522887906, 512381975, 502098773, 492033020, 482179592, 472533507, 463089928, 453844150, 444791600, 435927832, 427248521, 418749459, 410426553, 402275818, 394293377, 386475453, 378818371, 371318549, 363972499, 356776823, 349728208, 342823427, 336059334, 329432861, 322941017, 316580885]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 643).prefactor = (4851752300488561/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 643).cutoff/(generalMeanRows 643).c)).2 =
    (41504559546029/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 643).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 643).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 643).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 643

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 643).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 643).criticalRate j.val*(generalMeanRows 643).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 643).c*(generalMeanRows 643).criticalPoint j.val)).2-
      (generalMeanRows 643).J/2-(generalMeanRows 643).error (generalMeanGrid j.val)+
      (generalMeanRows 643).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 643).c)).2-
      (generalMeanRows 643).J/2-(generalMeanRows 643).error 4 := by
  have he : (generalMeanRows 643).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 643) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 643)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0643

/-! Kernel-checked entropy margins for general spectral rectangle 644. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0644
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4992486720, 4820501406, 4656285744, 4499391914, 4349403951, 4205934958, 4068624630, 3937137028, 3811158584, 3690396302, 3574576138, 3463441533, 3356752078, 3254282308, 3155820596, 3061168154, 2970138112, 2882554673, 2798252352, 2717075256, 2638876443, 2563517319, 2490867082, 2420802217, 2353206021, 2287968168, 2224984305, 2164155674, 2105388768, 2048595008, 1993690437, 1940595448, 1889234517, 1839535964, 1791431725, 1744857143, 1699750767, 1656054170, 1613711776, 1572670698, 1532880589, 1494293496, 1456863732, 1420547749, 1385304020, 1351092934, 1317876686, 1285619189, 1254285974, 1223844111, 1194262126, 1165509923, 1137558719, 1110380969, 1083950309, 1058241494, 1033230339, 1008893671, 985209274, 962155845, 939712949, 917860976, 896581098, 875855239, 855666031, 835996786, 816831462, 798154631, 779951456, 762207657, 744909490, 728043719, 711597600, 695558849, 679915630, 664656532, 649770548, 635247061, 621075827, 607246956, 593750899, 580578434, 567720651, 555168939, 542914976, 530950713, 519268365, 507860404, 496719541, 485838722, 475211118, 464830115, 454689306, 444782482, 435103629, 425646912, 416406677, 407377440, 398553880, 389930835, 381503295, 373266398, 365215423, 357345783, 349653027, 342132829, 334780984, 327593408, 320566130, 313695290, 306977133, 300408010, 293984368, 287702755, 281559807, 275552254, 269676912, 263930681, 258310543, 252813560, 247436870]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 644).prefactor = (607753659270583/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 644).cutoff/(generalMeanRows 644).c)).2 =
    (24191172122427/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 644).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 644).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 644).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 644

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 644).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 644).criticalRate j.val*(generalMeanRows 644).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 644).c*(generalMeanRows 644).criticalPoint j.val)).2-
      (generalMeanRows 644).J/2-(generalMeanRows 644).error (generalMeanGrid j.val)+
      (generalMeanRows 644).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 644).c)).2-
      (generalMeanRows 644).J/2-(generalMeanRows 644).error 4 := by
  have he : (generalMeanRows 644).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 644) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 644)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0644

/-! Kernel-checked entropy margins for general spectral rectangle 645. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0645
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5025310440, 4852194388, 4686899069, 4528973722, 4377999644, 4233587396, 4095374305, 3963022221, 3836215516, 3714659267, 3598077630, 3486212357, 3378821459, 3275677988, 3176568928, 3081294182, 2989665651, 2901506385, 2816649807, 2734939002, 2656226062, 2580371480, 2507243595, 2436718079, 2368677464, 2303010697, 2239612738, 2178384182, 2119230907, 2062063749, 2006798201, 1953354132, 1901655522, 1851630220, 1803209714, 1756328922, 1710925988, 1666942102, 1624321323, 1583010416, 1542958702, 1504117913, 1466442063, 1429887315, 1394411872, 1359975861, 1326541229, 1294071651, 1262532432, 1231890425, 1202113949, 1173172712, 1145037739, 1117681306, 1091076875, 1065199033, 1040023440, 1015526767, 991686654, 968481658, 945891208, 923895566, 902475781, 881613657, 861291713, 841493150, 822201821, 803402198, 785079343, 767218885, 749806989, 732830333, 716276086, 700131887, 684385820, 669026398, 654042545, 639423572, 625159167, 611239376, 597654588, 584395519, 571453200, 558818966, 546484437, 534441514, 522682359, 511199395, 499985285, 489032929, 478335452, 467886198, 457678717, 447706760, 437964271, 428445380, 419144394, 410055793, 401174221, 392494483, 384011536, 375720484, 367616576, 359695197, 351951864, 344382223, 336982043, 329747212, 322673732, 315757718, 308995392, 302383079, 295917205, 289594292, 283410957, 277363906, 271449936, 265665926, 260008838, 254475714, 249063674]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 645).prefactor = (2446997642784191/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 645).cutoff/(generalMeanRows 645).c)).2 =
    (24191172122427/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 645).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 645).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 645).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 645

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 645).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 645).criticalRate j.val*(generalMeanRows 645).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 645).c*(generalMeanRows 645).criticalPoint j.val)).2-
      (generalMeanRows 645).J/2-(generalMeanRows 645).error (generalMeanGrid j.val)+
      (generalMeanRows 645).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 645).c)).2-
      (generalMeanRows 645).J/2-(generalMeanRows 645).error 4 := by
  have he : (generalMeanRows 645).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 645) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 645)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0645

/-! Kernel-checked entropy margins for general spectral rectangle 646. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0646
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5877897164, 5687344784, 5505172792, 5330904682, 5164097589, 5004339350, 4851245883, 4704458841, 4563643512, 4428486920, 4298696119, 4173996652, 4054131143, 3938858032, 3827950411, 3721194973, 3618391043, 3519349693, 3423892938, 3331852983, 3243071546, 3157399223, 3074694908, 2994825257, 2917664189, 2843092428, 2770997074, 2701271213, 2633813545, 2568528046, 2505323649, 2444113946, 2384816918, 2327354674, 2271653211, 2217642193, 2165254736, 2114427218, 2065099093, 2017212718, 1970713192, 1925548209, 1881667910, 1839024756, 1797573399, 1757270565, 1718074948, 1679947100, 1642849337, 1606745645, 1571601598, 1537384269, 1504062161, 1471605127, 1439984307, 1409172061, 1379141911, 1349868478, 1321327433, 1293495442, 1266350121, 1239869986, 1214034412, 1188823594, 1164218503, 1140200853, 1116753066, 1093858236, 1071500103, 1049663017, 1028331916, 1007492295, 987130183, 967232118, 947785124, 928776692, 910194757, 892027677, 874264218, 856893538, 839905162, 823288975, 807035203, 791134398, 775577427, 760355456, 745459940, 730882610, 716615461, 702650744, 688980953, 675598819, 662497294, 649669551, 637108967, 624809123, 612763788, 600966921, 589412655, 578095296, 567009316, 556149344, 545510165, 535086708, 524874048, 514867395, 505062093, 495453611, 486037545, 476809607, 467765626, 458901541, 450213398, 441697349, 433349644, 425166630, 417144749, 409280534, 401570604, 394011666, 386600506]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 646).prefactor = (5161203133220303/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 646).cutoff/(generalMeanRows 646).c)).2 =
    (39626141546283/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 646).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 646).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 646).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 646

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 646).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 646).criticalRate j.val*(generalMeanRows 646).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 646).c*(generalMeanRows 646).criticalPoint j.val)).2-
      (generalMeanRows 646).J/2-(generalMeanRows 646).error (generalMeanGrid j.val)+
      (generalMeanRows 646).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 646).c)).2-
      (generalMeanRows 646).J/2-(generalMeanRows 646).error 4 := by
  have he : (generalMeanRows 646).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 646) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 646)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0646

/-! Kernel-checked entropy margins for general spectral rectangle 647. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0647
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4872591141, 4700224184, 4535681377, 4378514185, 4228305828, 4084668508, 3947240939, 3815686133, 3689689414, 3568956629, 3453212532, 3342199326, 3235675337, 3133413810, 3035201812, 2940839234, 2850137880, 2762920622, 2679020643, 2598280724, 2520552602, 2445696371, 2373579932, 2304078483, 2237074054, 2172455068, 2110115941, 2049956704, 1991882664, 1935804075, 1881635841, 1829297237, 1778711650, 1729806334, 1682512187, 1636763537, 1592497949, 1549656037, 1508181291, 1468019919, 1429120695, 1391434811, 1354915756, 1319519179, 1285202779, 1251926195, 1219650898, 1188340099, 1157958655, 1128472983, 1099850980, 1072061946, 1045076513, 1018866575, 993405229, 968666710, 944626336, 921260455, 898546392, 876462407, 854987640, 834102080, 813786514, 794022497, 774792310, 756078928, 737865991, 720137765, 702879123, 686075509, 669712918, 653777866, 638257371, 623138930, 608410493, 594060451, 580077610, 566451177, 553170741, 540226255, 527608027, 515306697, 503313228, 491618892, 480215255, 469094168, 458247755, 447668397, 437348730, 427281628, 417460198, 407877766, 398527874, 389404269, 380500894, 371811882, 363331549, 355054386, 346975055, 339088378, 331389336, 323873061, 316534829, 309370059, 302374303, 295543244, 288872694, 282358582, 275996957, 269783983, 263715929, 257789174, 252000197, 246345576, 240821985, 235426190, 230155046, 225005496, 219974564, 215059356, 210257058]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 647).prefactor = (4872447603899967/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 647).cutoff/(generalMeanRows 647).c)).2 =
    (366782368247467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 647).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 647).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 647).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 647

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 647).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 647).criticalRate j.val*(generalMeanRows 647).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 647).c*(generalMeanRows 647).criticalPoint j.val)).2-
      (generalMeanRows 647).J/2-(generalMeanRows 647).error (generalMeanGrid j.val)+
      (generalMeanRows 647).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 647).c)).2-
      (generalMeanRows 647).J/2-(generalMeanRows 647).error 4 := by
  have he : (generalMeanRows 647).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 647) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 647)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0647

/-! Kernel-checked entropy margins for general spectral rectangle 648. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0648
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5683768799, 5491505706, 5307755740, 5132038292, 4963906504, 4802944324, 4648763876, 4501003114, 4359323709, 4223409154, 4092963051, 3967707565, 3847382021, 3731741631, 3620556330, 3513609723, 3410698117, 3311629636, 3216223408, 3124308824, 3035724848, 2950319388, 2867948715, 2788476922, 2711775430, 2637722522, 2566202926, 2497107406, 2430332407, 2365779704, 2303356087, 2242973063, 2184546584, 2127996783, 2073247737, 2020227243, 1968866603, 1919100430, 1870866466, 1824105405, 1778760731, 1734778571, 1692107548, 1650698648, 1610505094, 1571482228, 1533587401, 1496779866, 1461020681, 1426272614, 1392500059, 1359668951, 1327746688, 1296702059, 1266505174, 1237127397, 1208541288, 1180720541, 1153639931, 1127275260, 1101603311, 1076601796, 1052249316, 1028525320, 1005410060, 982884558, 960930571, 939530553, 918667627, 898325553, 878488699, 859142015, 840271007, 821861709, 803900664, 786374901, 769271911, 752579632, 736286424, 720381055, 704852682, 689690837, 674885409, 660426627, 646305053, 632511561, 619037329, 605873824, 593012792, 580446246, 568166456, 556165939, 544437448, 532973964, 521768689, 510815033, 500106609, 489637227, 479400881, 469391751, 459604185, 450032704, 440671986, 431516868, 422562335, 413803518, 405235687, 396854247, 388654732, 380632803, 372784242, 365104946, 357590927, 350238307, 343043311, 336002269, 329111607, 322367848, 315767608, 309307591, 302984589]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 648).prefactor = (5212160425684569/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 648).cutoff/(generalMeanRows 648).c)).2 =
    (73497089413129/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 648).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 648).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 648).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 648

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 648).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 648).criticalRate j.val*(generalMeanRows 648).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 648).c*(generalMeanRows 648).criticalPoint j.val)).2-
      (generalMeanRows 648).J/2-(generalMeanRows 648).error (generalMeanGrid j.val)+
      (generalMeanRows 648).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 648).c)).2-
      (generalMeanRows 648).J/2-(generalMeanRows 648).error 4 := by
  have he : (generalMeanRows 648).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 648) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 648)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0648

/-! Kernel-checked entropy margins for general spectral rectangle 649. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0649
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5093492471, 4924125418, 4762312770, 4607619408, 4459641210, 4318002343, 4182352846, 4052366463, 3927738699, 3808185076, 3693439543, 3583253055, 3477392273, 3375638388, 3277786046, 3183642371, 3093026073, 3005766627, 2921703522, 2840685574, 2762570292, 2687223294, 2614517768, 2544333980, 2476558807, 2411085322, 2347812391, 2286644315, 2227490491, 2170265094, 2114886789, 2061278454, 2009366931, 1959082791, 1910360109, 1863136261, 1817351732, 1772949940, 1729877061, 1688081879, 1647515637, 1608131895, 1569886411, 1532737008, 1496643472, 1461567435, 1427472284, 1394323062, 1362086380, 1330730336, 1300224436, 1270539519, 1241647690, 1213522254, 1186137654, 1159469413, 1133494082, 1108189184, 1083533171, 1059505372, 1036085956, 1013255884, 990996879, 969291382, 948122521, 927474077, 907330456, 887676656, 868498241, 849781316, 831512499, 813678903, 796268108, 779268141, 762667460, 746454931, 730619812, 715151734, 700040687, 685277002, 670851341, 656754678, 642978287, 629513733, 616352854, 603487756, 590910799, 578614585, 566591951, 554835960, 543339890, 532097226, 521101654, 510347050, 499827476, 489537171, 479470543, 469622167, 459986776, 450559254, 441334633, 432308086, 423474923, 414830588, 406370647, 398090794, 389986838, 382054704, 374290427, 366690149, 359250115, 351966669, 344836254, 337855403, 331020742, 324328982, 317776923, 311361441, 305079496, 298928123, 292904432]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 649).prefactor = (2381024479531417/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 649).cutoff/(generalMeanRows 649).c)).2 =
    (402830284434363/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 649).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 649).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 649).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 649

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 649).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 649).criticalRate j.val*(generalMeanRows 649).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 649).c*(generalMeanRows 649).criticalPoint j.val)).2-
      (generalMeanRows 649).J/2-(generalMeanRows 649).error (generalMeanGrid j.val)+
      (generalMeanRows 649).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 649).c)).2-
      (generalMeanRows 649).J/2-(generalMeanRows 649).error 4 := by
  have he : (generalMeanRows 649).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 649) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 649)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0649

/-! Kernel-checked entropy margins for general spectral rectangle 650. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0650
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4905146639, 4731628039, 4565985862, 4407768581, 4256556629, 4111959618, 3973613847, 3841180077, 3714341529, 3592802086, 3476284662, 3364529738, 3257294025, 3154349252, 3055481065, 2960488018, 2869180655, 2781380669, 2696920124, 2615640753, 2537393303, 2462036931, 2389438656, 2319472844, 2252020735, 2186970006, 2124214369, 2063653187, 2005191134, 1948737864, 1894207713, 1841519417, 1790595850, 1741363780, 1693753643, 1647699331, 1603137989, 1560009835, 1518257982, 1477828278, 1438669154, 1400731478, 1363968426, 1328335351, 1293789672, 1260290755, 1227799815, 1196279818, 1165695385, 1136012709, 1107199472, 1079224770, 1052059037, 1025673982, 1000042520, 975138714, 950937718, 927415721, 904549898, 882318361, 860700114, 839675010, 819223709, 799327641, 779968970, 761130558, 742795933, 724949259, 707575306, 690659421, 674187506, 658145986, 642521794, 627302340, 612475498, 598029578, 583953313, 570235837, 556866669, 543835697, 531133162, 518749643, 506676041, 494903571, 483423742, 472228352, 461309469, 450659427, 440270811, 430136447, 420249396, 410602941, 401190579, 392006016, 383043154, 374296088, 365759095, 357426630, 349293318, 341353947, 333603465, 326036971, 318649710, 311437069, 304394572, 297517873, 290802754, 284245119, 277840990, 271586505, 265477908, 259511555, 253683899, 247991498, 242431002, 236999155, 231692793, 226508837, 221444291, 216496243, 211661859]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 650).prefactor = (4905002143527213/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 650).cutoff/(generalMeanRows 650).c)).2 =
    (366782368247467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 650).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 650).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 650).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 650

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 650).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 650).criticalRate j.val*(generalMeanRows 650).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 650).c*(generalMeanRows 650).criticalPoint j.val)).2-
      (generalMeanRows 650).J/2-(generalMeanRows 650).error (generalMeanGrid j.val)+
      (generalMeanRows 650).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 650).c)).2-
      (generalMeanRows 650).J/2-(generalMeanRows 650).error 4 := by
  have he : (generalMeanRows 650).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 650) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 650)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0650

/-! Kernel-checked entropy margins for general spectral rectangle 651. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0651
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5259079054, 5089261775, 4926989367, 4771824412, 4623360806, 4481221020, 4345053658, 4214531267, 4089348370, 3969219692, 3853878568, 3743075490, 3636576801, 3534163497, 3435630145, 3340783894, 3249443565, 3161438828, 3076609441, 2994804548, 2915882045, 2839707985, 2766156036, 2695106976, 2626448230, 2560073444, 2495882080, 2433779055, 2373674393, 2315482911, 2259123921, 2204520960, 2151601527, 2100296852, 2050541670, 2002274014, 1955435023, 1909968760, 1865822043, 1822944288, 1781287361, 1740805438, 1701454878, 1663194098, 1625983463, 1589785175, 1554563175, 1520283050, 1486911939, 1454418458, 1422772614, 1391945736, 1361910402, 1332640379, 1304110557, 1276296893, 1249176358, 1222726882, 1196927307, 1171757344, 1147197526, 1123229171, 1099834339, 1076995799, 1054696996, 1032922014, 1011655549, 990882879, 970589837, 950762784, 931388585, 912454585, 893948591, 875858845, 858174009, 840883142, 823975688, 807441455, 791270598, 775453610, 759981298, 744844780, 730035464, 715545039, 701365463, 687488953, 673907971, 660615217, 647603619, 634866323, 622396685, 610188262, 598234804, 586530250, 575068715, 563844487, 552852020, 542085928, 531540978, 521212086, 511094308, 501182840, 491473009, 481960272, 472640207, 463508513, 454561002, 445793597, 437202332, 428783340, 420532857, 412447215, 404522840, 396756248, 389144045, 381682920, 374369644, 367201070, 360174126, 353285817, 346533219]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 651).prefactor = (4782983482317999/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 651).cutoff/(generalMeanRows 651).c)).2 =
    (423343391334143/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 651).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 651).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 651).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 651

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 651).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 651).criticalRate j.val*(generalMeanRows 651).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 651).c*(generalMeanRows 651).criticalPoint j.val)).2-
      (generalMeanRows 651).J/2-(generalMeanRows 651).error (generalMeanGrid j.val)+
      (generalMeanRows 651).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 651).c)).2-
      (generalMeanRows 651).J/2-(generalMeanRows 651).error 4 := by
  have he : (generalMeanRows 651).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 651) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 651)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0651

/-! Kernel-checked entropy margins for general spectral rectangle 652. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0652
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5126874408, 4956397350, 4793524208, 4637817010, 4488868986, 4346301841, 4209763319, 4078925025, 3953480472, 3833143313, 3717645756, 3606737123, 3500182547, 3397761783, 3299268132, 3204507455, 3113297273, 3025465942, 2940851900, 2859302974, 2780675736, 2704834926, 2631652900, 2561009139, 2492789779, 2426887190, 2363199578, 2301630617, 2242089108, 2184488665, 2128747419, 2074787743, 2022536002, 1971922307, 1922880304, 1875346958, 1829262365, 1784569571, 1741214399, 1699145298, 1658313191, 1618671335, 1580175196, 1542782322, 1506452234, 1471146314, 1436827709, 1403461232, 1371013276, 1339451730, 1308745899, 1278866432, 1249785251, 1221475485, 1193911410, 1167068390, 1140922821, 1115452079, 1090634474, 1066449201, 1042876297, 1019896602, 997491715, 975643963, 954336364, 933552594, 913276955, 893494347, 874190240, 855350647, 836962100, 819011625, 801486722, 784375340, 767665861, 751347078, 735408178, 719838724, 704628642, 689768199, 675247994, 661058943, 647192264, 633639465, 620392332, 607442919, 594783534, 582406732, 570305304, 558472266, 546900853, 535584507, 524516871, 513691783, 503103266, 492745519, 482612916, 472699996, 463001456, 453512147, 444227069, 435141364, 426250310, 417549321, 409033936, 400699818, 392542750, 384558630, 376743467, 369093378, 361604583, 354273402, 347096255, 340069653, 333190199, 326454583, 319859582, 313402054, 307078938, 300887250, 294824081]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 652).prefactor = (4793258667706813/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 652).cutoff/(generalMeanRows 652).c)).2 =
    (402830284434363/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 652).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 652).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 652).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 652

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 652).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 652).criticalRate j.val*(generalMeanRows 652).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 652).c*(generalMeanRows 652).criticalPoint j.val)).2-
      (generalMeanRows 652).J/2-(generalMeanRows 652).error (generalMeanGrid j.val)+
      (generalMeanRows 652).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 652).c)).2-
      (generalMeanRows 652).J/2-(generalMeanRows 652).error 4 := by
  have he : (generalMeanRows 652).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 652) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 652)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0652

/-! Kernel-checked entropy margins for general spectral rectangle 653. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0653
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5160475124, 4988880787, 4824940200, 4668212522, 4518288317, 4374786810, 4237353436, 4105657649, 3979390952, 3858265122, 3742010612, 3630375102, 3523122184, 3420030171, 3320891009, 3225509285, 3133701326, 3045294363, 2960125774, 2878042389, 2798899841, 2722561982, 2648900333, 2577793584, 2509127125, 2442792621, 2378687611, 2316715137, 2256783402, 2198805455, 2142698890, 2088385571, 2035791380, 1984845971, 1935482555, 1887637683, 1841251059, 1796265355, 1752626040, 1710281225, 1669181511, 1629279849, 1590531412, 1552893471, 1516325281, 1480787973, 1446244449, 1412659293, 1379998679, 1348230283, 1317323211, 1287247918, 1257976144, 1229480840, 1201736115, 1174717170, 1148400247, 1122762574, 1097782319, 1073438539, 1049711142, 1026580841, 1004029116, 982038178, 960590933, 939670949, 919262426, 899350166, 879919543, 860956478, 842447416, 824379296, 806739538, 789516011, 772697020, 756271287, 740227925, 724556432, 709246665, 694288829, 679673462, 665391418, 651433859, 637792237, 624458284, 611424003, 598681650, 586223733, 574042994, 562132405, 550485154, 539094642, 527954471, 517058437, 506400524, 495974894, 485775884, 475797996, 466035893, 456484393, 447138463, 437993211, 429043887, 420285873, 411714679, 403325940, 395115412, 387078966, 379212583, 371512357, 363974481, 356595254, 349371069, 342298415, 335373874, 328594114, 321955890, 315456041, 309091485, 302859217, 296756311]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 653).prefactor = (964934583959759/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 653).cutoff/(generalMeanRows 653).c)).2 =
    (402830284434363/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 653).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 653).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 653).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 653

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 653).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 653).criticalRate j.val*(generalMeanRows 653).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 653).c*(generalMeanRows 653).criticalPoint j.val)).2-
      (generalMeanRows 653).J/2-(generalMeanRows 653).error (generalMeanGrid j.val)+
      (generalMeanRows 653).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 653).c)).2-
      (generalMeanRows 653).J/2-(generalMeanRows 653).error 4 := by
  have he : (generalMeanRows 653).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 653) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 653)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0653

/-! Kernel-checked entropy margins for general spectral rectangle 654. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0654
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4925566091, 4751239304, 4584853110, 4425950274, 4274106025, 4128925216, 3990039803, 3857106579, 3729805139, 3607836054, 3490919217, 3378792346, 3271209632, 3167940504, 3068768509, 2973490287, 2881914638, 2793861663, 2709161981, 2627656005, 2549193284, 2473631887, 2400837843, 2330684620, 2263052644, 2197828857, 2134906302, 2074183740, 2015565302, 1958960152, 1904282184, 1851449738, 1800385332, 1751015418, 1703270147, 1657083156, 1612391366, 1569134795, 1527256380, 1486701812, 1447419387, 1409359853, 1372476282, 1336723938, 1302060161, 1268444253, 1235837374, 1204202440, 1173504037, 1143708324, 1114782961, 1086697022, 1059420928, 1032926379, 1007186282, 982174698, 957866782, 934238724, 911267705, 888931843, 867210149, 846082484, 825529519, 805532695, 786074185, 767136863, 748704269, 730760576, 713290567, 696279600, 679713585, 663578961, 647862668, 632552127, 617635218, 603100262, 588935998, 575131566, 561676492, 548560670, 535774344, 523308098, 511152836, 499299776, 487740428, 476466592, 465470336, 454743994, 444280149, 434071628, 424111487, 414393008, 404909686, 395655221, 386623511, 377808647, 369204901, 360806721, 352608726, 344605699, 336792578, 329164457, 321716572, 314444303, 307343164, 300408802, 293636988, 287023619, 280564706, 274256376, 268094867, 262076521, 256197783, 250455199, 244845409, 239365148, 234011239, 228780592, 223670201, 218677144, 213798574]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 654).prefactor = (4958559183587241/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 654).cutoff/(generalMeanRows 654).c)).2 =
    (372513042956451/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 654).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 654).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 654).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 654

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 654).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 654).criticalRate j.val*(generalMeanRows 654).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 654).c*(generalMeanRows 654).criticalPoint j.val)).2-
      (generalMeanRows 654).J/2-(generalMeanRows 654).error (generalMeanGrid j.val)+
      (generalMeanRows 654).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 654).c)).2-
      (generalMeanRows 654).J/2-(generalMeanRows 654).error 4 := by
  have he : (generalMeanRows 654).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 654) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 654)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0654

/-! Kernel-checked entropy margins for general spectral rectangle 655. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0655
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5040614457, 4864586473, 4696543184, 4536024627, 4382603520, 4235882417, 4095491154, 3961084576, 3832340487, 3708957804, 3590654897, 3477168079, 3368250246, 3263669628, 3163208669, 3066662986, 2973840434, 2884560243, 2798652223, 2715956041, 2636320553, 2559603188, 2485669382, 2414392053, 2345651117, 2279333044, 2215330438, 2153541654, 2093870443, 2036225620, 1980520753, 1926673877, 1874607229, 1824246996, 1775523084, 1728368903, 1682721159, 1638519669, 1595707184, 1554229222, 1514033910, 1475071845, 1437295952, 1400661358, 1365125275, 1330646880, 1297187217, 1264709095, 1233176992, 1202556968, 1172816587, 1143924831, 1115852035, 1088569810, 1062050986, 1036269543, 1011200558, 986820149, 963105422, 940034425, 917586100, 895740241, 874477451, 853779106, 833627314, 814004885, 794895295, 776282658, 758151691, 740487691, 723276510, 706504523, 690158609, 674226131, 658694908, 643553199, 628789684, 614393444, 600353944, 586661017, 573304849, 560275962, 547565201, 535163723, 523062979, 511254707, 499730916, 488483878, 477506118, 466790400, 456329721, 446117302, 436146575, 426411182, 416904960, 407621938, 398556328, 389702516, 381055062, 372608687, 364358270, 356298841, 348425579, 340733800, 333218960, 325876645, 318702567, 311692560, 304842577, 298148686, 291607063, 285213992, 278965859, 272859150, 266890447, 261056425, 255353850, 249779573, 244330531, 239003744, 233796306]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 655).prefactor = (4991159842791583/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 655).cutoff/(generalMeanRows 655).c)).2 =
    (379759451477219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 655).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 655).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 655).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 655

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 655).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 655).criticalRate j.val*(generalMeanRows 655).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 655).c*(generalMeanRows 655).criticalPoint j.val)).2-
      (generalMeanRows 655).J/2-(generalMeanRows 655).error (generalMeanGrid j.val)+
      (generalMeanRows 655).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 655).c)).2-
      (generalMeanRows 655).J/2-(generalMeanRows 655).error 4 := by
  have he : (generalMeanRows 655).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 655) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 655)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0655

/-! Kernel-checked entropy margins for general spectral rectangle 656. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0656
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4974240484, 4801802004, 4637146478, 4479826548, 4329426632, 4185560145, 4047867031, 3916011539, 3789680237, 3668580216, 3552437476, 3440995460, 3334013725, 3231266739, 3132542780, 3037642937, 2946380191, 2858578579, 2774072424, 2692705630, 2614331034, 2538809806, 2466010899, 2395810542, 2328091766, 2262743972, 2199662528, 2138748391, 2079907768, 2023051783, 1968096189, 1914961081, 1863570638, 1813852883, 1765739455, 1719165402, 1674068977, 1630391461, 1588076987, 1547072381, 1507327011, 1468792642, 1431423309, 1395175190, 1360006489, 1325877327, 1292749639, 1260587080, 1229354929, 1199020008, 1169550599, 1140916371, 1113088305, 1086038631, 1059740759, 1034169227, 1009299637, 985108609, 961573723, 938673479, 916387249, 894695234, 873578426, 853018568, 832998120, 813500225, 794508678, 776007893, 757982876, 740419199, 723302972, 706620819, 690359857, 674507671, 659052298, 643982200, 629286252, 614953720, 600974248, 587337837, 574034833, 561055913, 548392070, 536034598, 523975083, 512205390, 500717651, 489504253, 478557832, 467871258, 457437629, 447250263, 437302685, 427588624, 418102003, 408836929, 399787693, 390948755, 382314744, 373880449, 365640814, 357590930, 349726034, 342041500, 334532838, 327195683, 320025799, 313019066, 306171484, 299479161, 292938317, 286545275, 280296458, 274188390, 268217686, 262381056, 256675296, 251097290, 245644002, 240312479, 235099846]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 656).prefactor = (977624085058579/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 656).cutoff/(generalMeanRows 656).c)).2 =
    (95252809259931/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 656).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 656).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 656).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 656

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 656).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 656).criticalRate j.val*(generalMeanRows 656).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 656).c*(generalMeanRows 656).criticalPoint j.val)).2-
      (generalMeanRows 656).J/2-(generalMeanRows 656).error (generalMeanGrid j.val)+
      (generalMeanRows 656).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 656).c)).2-
      (generalMeanRows 656).J/2-(generalMeanRows 656).error 4 := by
  have he : (generalMeanRows 656).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 656) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 656)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0656

/-! Kernel-checked entropy margins for general spectral rectangle 657. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0657
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5039654898, 4864948743, 4698127892, 4538739105, 4386361335, 4240602913, 4101099047, 3967509572, 3839516933, 3716824370, 3599154280, 3486246730, 3377858118, 3273759944, 3173737702, 3077589866, 2985126958, 2896170699, 2810553234, 2728116415, 2648711143, 2572196763, 2498440505, 2427316968, 2358707648, 2292500489, 2228589484, 2166874288, 2107259872, 2049656196, 1993977901, 1940144032, 1888077772, 1837706197, 1788960048, 1741773516, 1696084044, 1651832141, 1608961205, 1567417363, 1527149316, 1488108196, 1450247433, 1413522628, 1377891436, 1343313453, 1309750116, 1277164598, 1245521725, 1214787880, 1184930930, 1155920144, 1127726122, 1100320727, 1073677022, 1047769207, 1022572567, 998063411, 974219026, 951017630, 928438322, 906461044, 885066536, 864236302, 843952573, 824198268, 804956971, 786212889, 767950831, 750156181, 732814864, 715913330, 699438526, 683377875, 667719253, 652450974, 637561765, 623040751, 608877440, 595061701, 581583755, 568434154, 555603773, 543083792, 530865687, 518941215, 507302405, 495941544, 484851170, 474024061, 463453224, 453131887, 443053493, 433211686, 423600309, 414213394, 405045154, 396089979, 387342425, 378797214, 370449222, 362293477, 354325153, 346539563, 338932156, 331498514, 324234341, 317135465, 310197833, 303417502, 296790641, 290313527, 283982534, 277794141, 271744919, 265831533, 260050739, 254399378, 248874376, 243472741, 238191558]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 657).prefactor = (2476201152840227/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 657).cutoff/(generalMeanRows 657).c)).2 =
    (95252809259931/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 657).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 657).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 657).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 657

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 657).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 657).criticalRate j.val*(generalMeanRows 657).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 657).c*(generalMeanRows 657).criticalPoint j.val)).2-
      (generalMeanRows 657).J/2-(generalMeanRows 657).error (generalMeanGrid j.val)+
      (generalMeanRows 657).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 657).c)).2-
      (generalMeanRows 657).J/2-(generalMeanRows 657).error 4 := by
  have he : (generalMeanRows 657).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 657) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 657)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0657

/-! Kernel-checked entropy margins for general spectral rectangle 658. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0658
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7797508124, 7567580301, 7346759867, 7134572603, 6930576900, 6734360810, 6545539427, 6363752564, 6188662686, 6019953058, 5857326089, 5700501839, 5549216680, 5403222075, 5262283485, 5126179365, 4994700257, 4867647961, 4744834778, 4626082813, 4511223340, 4400096220, 4292549358, 4188438207, 4087625312, 3989979885, 3895377408, 3803699275, 3714832447, 3628669141, 3545106537, 3464046503, 3385395339, 3309063543, 3234965582, 3163019689, 3093147666, 3025274697, 2959329180, 2895242564, 2832949199, 2772386186, 2713493252, 2656212614, 2600488866, 2546268862, 2493501608, 2442138168, 2392131560, 2343436672, 2296010172, 2249810432, 2204797446, 2160932761, 2118179407, 2076501831, 2035865834, 1996238515, 1957588212, 1919884448, 1883097883, 1847200265, 1812164383, 1777964024, 1744573928, 1711969755, 1680128040, 1649026164, 1618642311, 1588955444, 1559945265, 1531592194, 1503877332, 1476782440, 1450289908, 1424382734, 1399044498, 1374259340, 1350011937, 1326287484, 1303071673, 1280350671, 1258111109, 1236340058, 1215025012, 1194153877, 1173714953, 1153696916, 1134088811, 1114880030, 1096060305, 1077619695, 1059548572, 1041837609, 1024477771, 1007460306, 990776728, 974418817, 958378600, 942648350, 927220571, 912087995, 897243571, 882680456, 868392013, 854371799, 840613558, 827111220, 813858888, 800850837, 788081504, 775545487, 763237535, 751152547, 739285563, 727631764, 716186462, 704945101, 693903246, 683056588, 672400930]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 658).prefactor = (2568040624906301/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 658).cutoff/(generalMeanRows 658).c)).2 =
    (76618642950291/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 658).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 658).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 658).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 658

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 658).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 658).criticalRate j.val*(generalMeanRows 658).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 658).c*(generalMeanRows 658).criticalPoint j.val)).2-
      (generalMeanRows 658).J/2-(generalMeanRows 658).error (generalMeanGrid j.val)+
      (generalMeanRows 658).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 658).c)).2-
      (generalMeanRows 658).J/2-(generalMeanRows 658).error 4 := by
  have he : (generalMeanRows 658).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 658) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 658)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0658

/-! Kernel-checked entropy margins for general spectral rectangle 659. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0659
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7376050742, 7166607209, 6965580287, 6772523552, 6587021317, 6408685875, 6237155060, 6072090078, 5913173568, 5760107869, 5612613460, 5470427562, 5333302870, 5201006407, 5073318489, 4950031774, 4830950407, 4715889232, 4604673071, 4497136068, 4393121079, 4292479120, 4195068851, 4100756103, 4009413441, 3920919756, 3835159894, 3752024303, 3671408713, 3593213830, 3517345059, 3443712244, 3372229416, 3302814573, 3235389461, 3169879376, 3106212977, 3044322109, 2984141638, 2925609299, 2868665545, 2813253413, 2759318395, 2706808318, 2655673224, 2605865265, 2557338604, 2510049312, 2463955282, 2419016140, 2375193165, 2332449211, 2290748633, 2250057221, 2210342130, 2171571820, 2133715997, 2096745559, 2060632536, 2025350047, 1990872247, 1957174284, 1924232256, 1892023164, 1860524882, 1829716111, 1799576349, 1770085854, 1741225613, 1712977309, 1685323298, 1658246572, 1631730739, 1605759994, 1580319098, 1555393351, 1530968573, 1507031079, 1483567666, 1460565584, 1438012525, 1415896604, 1394206340, 1372930639, 1352058785, 1331580417, 1311485522, 1291764416, 1272407735, 1253406419, 1234751706, 1216435114, 1198448434, 1180783719, 1163433274, 1146389647, 1129645618, 1113194192, 1097028591, 1081142244, 1065528781, 1050182024, 1035095983, 1020264846, 1005682974, 991344892, 977245291, 963379010, 949741042, 936326523, 923130726, 910149058, 897377058, 884810386, 872444826, 860276274, 848300742, 836514347, 824913315, 813493968, 802252730]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 659).prefactor = (2420298610154109/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 659).cutoff/(generalMeanRows 659).c)).2 =
    (356143170461711/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 659).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 659).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 659).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 659

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 659).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 659).criticalRate j.val*(generalMeanRows 659).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 659).c*(generalMeanRows 659).criticalPoint j.val)).2-
      (generalMeanRows 659).J/2-(generalMeanRows 659).error (generalMeanGrid j.val)+
      (generalMeanRows 659).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 659).c)).2-
      (generalMeanRows 659).J/2-(generalMeanRows 659).error 4 := by
  have he : (generalMeanRows 659).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 659) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 659)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0659

/-! Kernel-checked entropy margins for general spectral rectangle 660. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0660
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6883816540, 6666203608, 6457471109, 6257151755, 6064810297, 5880040661, 5702463398, 5531723426, 5367488011, 5209444956, 5057300983, 4910780265, 4769623115, 4633584789, 4502434402, 4375953946, 4253937394, 4136189876, 4022526939, 3912773851, 3806764977, 3704343195, 3605359366, 3509671835, 3417145983, 3327653796, 3241073484, 3157289110, 3076190257, 2997671714, 2921633184, 2847979009, 2776617921, 2707462798, 2640430448, 2575441395, 2512419688, 2451292719, 2391991045, 2334448236, 2278600714, 2224387616, 2171750661, 2120634015, 2070984183, 2022749887, 1975881964, 1930333265, 1886058559, 1843014447, 1801159270, 1760453034, 1720857334, 1682335279, 1644851423, 1608371704, 1572863379, 1538294968, 1504636194, 1471857936, 1439932175, 1408831947, 1378531298, 1349005240, 1320229712, 1292181539, 1264838393, 1238178761, 1212181911, 1186827857, 1162097329, 1137971744, 1114433180, 1091464346, 1069048557, 1047169713, 1025812272, 1004961227, 984602088, 964720862, 945304030, 926338529, 907811739, 889711459, 872025896, 854743647, 837853685, 821345344, 805208307, 789432589, 774008529, 758926777, 744178278, 729754268, 715646258, 701846026, 688345608, 675137286, 662213581, 649567246, 637191253, 625078789, 613223249, 601618223, 590257498, 579135041, 568245003, 557581702, 547139628, 536913428, 526897905, 517088014, 507478852, 498065659, 488843807, 479808801, 470956273, 462281974, 453781776, 445451665, 437287736]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 660).prefactor = (5072090470121393/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 660).cutoff/(generalMeanRows 660).c)).2 =
    (72826412741601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 660).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 660).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 660).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 660

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 660).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 660).criticalRate j.val*(generalMeanRows 660).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 660).c*(generalMeanRows 660).criticalPoint j.val)).2-
      (generalMeanRows 660).J/2-(generalMeanRows 660).error (generalMeanGrid j.val)+
      (generalMeanRows 660).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 660).c)).2-
      (generalMeanRows 660).J/2-(generalMeanRows 660).error 4 := by
  have he : (generalMeanRows 660).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 660) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 660)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0660

/-! Kernel-checked entropy margins for general spectral rectangle 661. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0661
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6758232397, 6561563661, 6372964384, 6191999516, 6018264040, 5851380306, 5690995668, 5536780376, 5388425695, 5245642214, 5108158328, 4975718869, 4848083869, 4725027437, 4606336741, 4491811082, 4381261044, 4274507727, 4171382032, 4071724016, 3975382295, 3882213491, 3792081726, 3704858159, 3620420546, 3538652843, 3459444835, 3382691789, 3308294136, 3236157169, 3166190767, 3098309138, 3032430573, 2968477221, 2906374880, 2846052797, 2787443482, 2730482535, 2675108484, 2621262628, 2568888898, 2517933719, 2468345882, 2420076423, 2373078516, 2327307359, 2282720076, 2239275625, 2196934706, 2155659674, 2115414465, 2076164514, 2037876687, 2000519214, 1964061621, 1928474674, 1893730316, 1859801619, 1826662724, 1794288802, 1762655996, 1731741387, 1701522946, 1671979494, 1643090668, 1614836881, 1587199288, 1560159758, 1533700837, 1507805721, 1482458228, 1457642771, 1433344334, 1409548443, 1386241150, 1363409003, 1341039032, 1319118725, 1297636010, 1276579235, 1255937154, 1235698908, 1215854009, 1196392326, 1177304072, 1158579784, 1140210318, 1122186831, 1104500771, 1087143864, 1070108105, 1053385746, 1036969287, 1020851465, 1005025246, 989483816, 974220572, 959229116, 944503243, 930036939, 915824369, 901859874, 888137962, 874653303, 861400724, 848375201, 835571854, 822985944, 810612866, 798448143, 786487427, 774726485, 763161206, 751787586, 740601735, 729599862, 718778281, 708133401, 697661728, 687359856, 677224470]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 661).prefactor = (4731836402583637/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 661).cutoff/(generalMeanRows 661).c)).2 =
    (92477003176991/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 661).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 661).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 661).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 661

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 661).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 661).criticalRate j.val*(generalMeanRows 661).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 661).c*(generalMeanRows 661).criticalPoint j.val)).2-
      (generalMeanRows 661).J/2-(generalMeanRows 661).error (generalMeanGrid j.val)+
      (generalMeanRows 661).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 661).c)).2-
      (generalMeanRows 661).J/2-(generalMeanRows 661).error 4 := by
  have he : (generalMeanRows 661).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 661) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 661)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0661

/-! Kernel-checked entropy margins for general spectral rectangle 662. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0662
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6266680433, 6063974549, 5869734859, 5683508476, 5504873628, 5333436894, 5168830762, 5010711448, 4858756940, 4712665254, 4572152861, 4436953270, 4306815745, 4181504146, 4060795872, 3944480904, 3832360929, 3724248538, 3619966494, 3519347061, 3422231386, 3328468928, 3237916937, 3150439968, 3065909432, 2984203186, 2905205143, 2828804920, 2754897504, 2683382943, 2614166060, 2547156184, 2482266899, 2419415813, 2358524335, 2299517473, 2242323644, 2186874489, 2133104708, 2080951900, 2030356415, 1981261213, 1933611731, 1887355762, 1842443335, 1798826605, 1756459750, 1715298874, 1675301908, 1636428530, 1598640077, 1561899470, 1526171134, 1491420936, 1457616109, 1424725197, 1392717992, 1361565475, 1331239765, 1301714067, 1272962624, 1244960670, 1217684386, 1191110862, 1165218049, 1139984731, 1115390485, 1091415643, 1068041267, 1045249114, 1023021605, 1001341801, 980193373, 959560578, 939428237, 919781705, 900606856, 881890058, 863618156, 845778448, 828358672, 811346984, 794731944, 778502500, 762647970, 747158032, 732022705, 717232340, 702777603, 688649467, 674839197, 661338341, 648138719, 635232412, 622611750, 610269307, 598197892, 586390534, 574840482, 563541190, 552486316, 541669707, 531085401, 520727611, 510590728, 500669307, 490958063, 481451870, 472145750, 463034870, 454114536, 445380190, 436827405, 428451878, 420249428, 412215994, 404347624, 396640480, 389090828, 381695037, 374449574]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 662).prefactor = (615778783213631/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 662).cutoff/(generalMeanRows 662).c)).2 =
    (61750717910927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 662).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 662).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 662).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 662

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 662).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 662).criticalRate j.val*(generalMeanRows 662).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 662).c*(generalMeanRows 662).criticalPoint j.val)).2-
      (generalMeanRows 662).J/2-(generalMeanRows 662).error (generalMeanGrid j.val)+
      (generalMeanRows 662).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 662).c)).2-
      (generalMeanRows 662).J/2-(generalMeanRows 662).error 4 := by
  have he : (generalMeanRows 662).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 662) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 662)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0662

/-! Kernel-checked entropy margins for general spectral rectangle 663. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0663
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5991209708, 5796657210, 5610313045, 5431733802, 5260506612, 5096246459, 4938593783, 4787212345, 4641787314, 4502023554, 4367644080, 4238388667, 4114012588, 3994285478, 3878990288, 3767922349, 3660888503, 3557706318, 3458203363, 3362216548, 3269591512, 3180182065, 3093849665, 3010462947, 2929897274, 2852034334, 2776761756, 2703972757, 2633565821, 2565444386, 2499516564, 2435694877, 2373896008, 2314040570, 2256052893, 2199860817, 2145395508, 2092591275, 2041385408, 1991718022, 1943531904, 1896772383, 1851387193, 1807326357, 1764542066, 1722988575, 1682622098, 1643400712, 1605284266, 1568234296, 1532213942, 1497187869, 1463122200, 1429984443, 1397743425, 1366369235, 1335833158, 1306107629, 1277166172, 1248983354, 1221534738, 1194796836, 1168747071, 1143363729, 1118625927, 1094513573, 1071007334, 1048088600, 1025739455, 1003942643, 982681547, 961940154, 941703034, 921955313, 902682652, 883871221, 865507683, 847579167, 830073256, 812977962, 796281713, 779973334, 764042030, 748477375, 733269291, 718408041, 703884209, 689688692, 675812687, 662247677, 648985422, 636017948, 623337537, 610936716, 598808249, 586945128, 575340563, 563987977, 552880992, 542013431, 531379302, 520972794, 510788274, 500820275, 491063492, 481512781, 472163144, 463009731, 454047835, 445272880, 436680426, 428266155, 420025875, 411955511, 404051100, 396308790, 388724839, 381295602, 374017538, 366887201, 359901236]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 663).prefactor = (75477751246073/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 663).cutoff/(generalMeanRows 663).c)).2 =
    (322868381576841/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 663).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 663).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 663).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 663

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 663).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 663).criticalRate j.val*(generalMeanRows 663).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 663).c*(generalMeanRows 663).criticalPoint j.val)).2-
      (generalMeanRows 663).J/2-(generalMeanRows 663).error (generalMeanGrid j.val)+
      (generalMeanRows 663).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 663).c)).2-
      (generalMeanRows 663).J/2-(generalMeanRows 663).error 4 := by
  have he : (generalMeanRows 663).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 663) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 663)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0663

/-! Kernel-checked entropy margins for general spectral rectangle 664. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0664
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5819887478, 5633441871, 5454911331, 5283863282, 5119895090, 4962631440, 4811721984, 4666839257, 4527676804, 4393947499, 4265382033, 4141727545, 4022746387, 3908215002, 3797922905, 3691671750, 3589274486, 3490554575, 3395345286, 3303489041, 3214836808, 3129247559, 3046587750, 2966730854, 2889556924, 2814952194, 2742808695, 2673023917, 2605500481, 2540145841, 2476872001, 2415595256, 2356235951, 2298718247, 2242969917, 2188922138, 2136509312, 2085668887, 2036341197, 1988469304, 1941998858, 1896877957, 1853057024, 1810488686, 1769127657, 1728930638, 1689856212, 1651864753, 1614918332, 1578980640, 1544016900, 1509993801, 1476879420, 1444643158, 1413255675, 1382688834, 1352915639, 1323910183, 1295647599, 1268104010, 1241256482, 1215082984, 1189562343, 1164674208, 1140399011, 1116717931, 1093612865, 1071066390, 1049061738, 1027582764, 1006613921, 986140231, 966147265, 946621114, 927548371, 908916107, 890711853, 872923579, 855539675, 838548937, 821940544, 805704050, 789829361, 774306728, 759126725, 744280244, 729758476, 715552904, 701655286, 688057650, 674752278, 661731702, 648988688, 636516231, 624307546, 612356058, 600655396, 589199382, 577982029, 566997528, 556240247, 545704720, 535385643, 525277869, 515376401, 505676385, 496173110, 486861996, 477738596, 468798587, 460037767, 451452053, 443037472, 434790161, 426706364, 418782425, 411014787, 403399988, 395934658, 388615517, 381439369]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 664).prefactor = (944681059322653/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 664).cutoff/(generalMeanRows 664).c)).2 =
    (347296566321419/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 664).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 664).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 664).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 664

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 664).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 664).criticalRate j.val*(generalMeanRows 664).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 664).c*(generalMeanRows 664).criticalPoint j.val)).2-
      (generalMeanRows 664).J/2-(generalMeanRows 664).error (generalMeanGrid j.val)+
      (generalMeanRows 664).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 664).c)).2-
      (generalMeanRows 664).J/2-(generalMeanRows 664).error 4 := by
  have he : (generalMeanRows 664).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 664) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 664)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0664

/-! Kernel-checked entropy margins for general spectral rectangle 665. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0665
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5704062489, 5525904657, 5355340127, 5191948246, 5035337679, 4885143842, 4741026612, 4602668286, 4469771743, 4342058801, 4219268732, 4101156924, 3987493662, 3878063031, 3772661911, 3671099064, 3573194298, 3478777705, 3387688961, 3299776682, 3214897832, 3132917181, 3053706800, 2977145599, 2903118897, 2831518025, 2762239956, 2695186965, 2630266310, 2567389935, 2506474199, 2447439615, 2390210612, 2334715314, 2280885326, 2228655545, 2177963971, 2128751541, 2080961966, 2034541580, 1989439202, 1945605998, 1902995363, 1861562797, 1821265803, 1782063773, 1743917902, 1706791085, 1670647839, 1635454214, 1601177724, 1567787266, 1535253055, 1503546562, 1472640447, 1442508505, 1413125608, 1384467657, 1356511530, 1329235036, 1302616871, 1276636579, 1251274506, 1226511771, 1202330223, 1178712412, 1155641555, 1133101505, 1111076727, 1089552263, 1068513712, 1047947205, 1027839376, 1008177349, 988948706, 970141478, 951744117, 933745481, 916134820, 898901752, 882036255, 865528647, 849369574, 833549997, 818061175, 802894660, 788042276, 773496116, 759248527, 745292101, 731619665, 718224273, 705099194, 692237906, 679634089, 667281613, 655174538, 643307096, 631673697, 620268912, 609087473, 598124264, 587374317, 576832807, 566495044, 556356474, 546412666, 536659314, 527092230, 517707342, 508500687, 499468408, 490606752, 481912065, 473380791, 465009464, 456794710, 448733241, 440821852, 433057422, 425436907]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 665).prefactor = (921437395400613/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 665).cutoff/(generalMeanRows 665).c)).2 =
    (377734820207869/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 665).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 665).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 665).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 665

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 665).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 665).criticalRate j.val*(generalMeanRows 665).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 665).c*(generalMeanRows 665).criticalPoint j.val)).2-
      (generalMeanRows 665).J/2-(generalMeanRows 665).error (generalMeanGrid j.val)+
      (generalMeanRows 665).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 665).c)).2-
      (generalMeanRows 665).J/2-(generalMeanRows 665).error 4 := by
  have he : (generalMeanRows 665).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 665) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 665)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0665

/-! Kernel-checked entropy margins for general spectral rectangle 666. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0666
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5261277176, 5086424835, 4919165256, 4759076957, 4605767816, 4458872505, 4318050199, 4182982533, 4053371767, 3928939141, 3809423382, 3694579373, 3584176924, 3477999677, 3375844100, 3277518566, 3182842522, 3091645721, 3003767518, 2919056229, 2837368537, 2758568943, 2682529266, 2609128176, 2538250762, 2469788138, 2403637067, 2339699625, 2277882876, 2218098579, 2160262913, 2104296217, 2050122751, 1997670473, 1946870829, 1897658557, 1849971506, 1803750460, 1758938982, 1715483264, 1673331978, 1632436154, 1592749046, 1554226021, 1516824445, 1480503581, 1445224492, 1410949948, 1377644338, 1345273591, 1313805097, 1283207634, 1253451302, 1224507455, 1196348641, 1168948545, 1142281930, 1116324592, 1091053306, 1066445780, 1042480613, 1019137253, 996395954, 974237745, 952644389, 931598351, 911082767, 891081414, 871578680, 852559537, 834009515, 815914679, 798261602, 781037346, 764229443, 747825866, 731815021, 716185720, 700927169, 686028949, 671481002, 657273613, 643397399, 629843295, 616602540, 603666663, 591027475, 578677056, 566607744, 554812126, 543283024, 532013494, 520996808, 510226451, 499696113, 489399678, 479331218, 469484989, 459855419, 450437105, 441224807, 432213438, 423398065, 414773897, 406336285, 398080712, 390002794, 382098269, 374363000, 366792964, 359384251, 352133060, 345035697, 338088568, 331288177, 324631123, 318114099, 311733885, 305487347, 299371433, 293383175]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 666).prefactor = (4617694226982883/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 666).cutoff/(generalMeanRows 666).c)).2 =
    (352646216068659/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 666).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 666).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 666).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 666

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 666).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 666).criticalRate j.val*(generalMeanRows 666).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 666).c*(generalMeanRows 666).criticalPoint j.val)).2-
      (generalMeanRows 666).J/2-(generalMeanRows 666).error (generalMeanGrid j.val)+
      (generalMeanRows 666).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 666).c)).2-
      (generalMeanRows 666).J/2-(generalMeanRows 666).error 4 := by
  have he : (generalMeanRows 666).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 666) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 666)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0666

/-! Kernel-checked entropy margins for general spectral rectangle 667. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0667
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5270107067, 5097070189, 4931580446, 4773214886, 4621580175, 4476310007, 4337062797, 4203519618, 4075382351, 3952372020, 3834227293, 3720703122, 3611569520, 3506610436, 3405622749, 3308415334, 3214808219, 3124631809, 3037726178, 2953940413, 2873132019, 2795166360, 2719916154, 2647261002, 2577086949, 2509286085, 2443756168, 2380400279, 2319126498, 2259847607, 2202480807, 2146947465, 2093172862, 2041085976, 1990619264, 1941708471, 1894292439, 1848312937, 1803714500, 1760444276, 1718451884, 1677689279, 1638110631, 1599672200, 1562332233, 1526050853, 1490789966, 1456513165, 1423185648, 1390774130, 1359246769, 1328573094, 1298723935, 1269671358, 1241388604, 1213850032, 1187031063, 1160908128, 1135458623, 1110660857, 1086494013, 1062938104, 1039973935, 1017583065, 995747773, 974451024, 953676436, 933408255, 913631320, 894331039, 875493365, 857104771, 839152225, 821623168, 804505498, 787787543, 771458049, 755506158, 739921391, 724693634, 709813122, 695270424, 681056427, 667162328, 653579614, 640300059, 627315703, 614618848, 602202046, 590058086, 578179988, 566560994, 555194557, 544074333, 533194176, 522548128, 512130411, 501935423, 491957730, 482192060, 472633296, 463276471, 454116764, 445149491, 436370105, 427774187, 419357443, 411115700, 403044902, 395141104, 387400471, 379819272, 372393877, 365120753, 357996465, 351017666, 344181098, 337483589, 330922052, 324493476, 318194930]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 667).prefactor = (922462164526521/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 667).cutoff/(generalMeanRows 667).c)).2 =
    (371511862289941/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 667).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 667).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 667).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 667

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 667).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 667).criticalRate j.val*(generalMeanRows 667).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 667).c*(generalMeanRows 667).criticalPoint j.val)).2-
      (generalMeanRows 667).J/2-(generalMeanRows 667).error (generalMeanGrid j.val)+
      (generalMeanRows 667).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 667).c)).2-
      (generalMeanRows 667).J/2-(generalMeanRows 667).error 4 := by
  have he : (generalMeanRows 667).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 667) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 667)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0667

/-! Kernel-checked entropy margins for general spectral rectangle 668. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0668
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5284790399, 5115778568, 4954124743, 4799413224, 4651257580, 4509298090, 4373199466, 4242648809, 4117353780, 3997040950, 3881454322, 3770353980, 3663514876, 3560725724, 3461787992, 3366514986, 3274731011, 3186270601, 3100977817, 3018705602, 2939315184, 2862675527, 2788662831, 2717160061, 2648056517, 2581247434, 2516633613, 2454121077, 2393620752, 2335048171, 2278323196, 2223369764, 2170115645, 2118492219, 2068434268, 2019879782, 1972769774, 1927048111, 1882661354, 1839558610, 1797691389, 1757013473, 1717480796, 1679051321, 1641684940, 1605343364, 1569990031, 1535590015, 1502109937, 1469517891, 1437783362, 1406877161, 1376771352, 1347439191, 1318855068, 1290994446, 1263833814, 1237350631, 1211523279, 1186331022, 1161753961, 1137772992, 1114369770, 1091526673, 1069226767, 1047453776, 1026192048, 1005426526, 985142726, 965326703, 945965034, 927044789, 908553510, 890479192, 872810262, 855535557, 838644311, 822126135, 805971000, 790169222, 774711450, 759588649, 744792085, 730313318, 716144184, 702276790, 688703494, 675416904, 662409863, 649675438, 637206917, 624997794, 613041765, 601332719, 589864730, 578632049, 567629101, 556850474, 546290915, 535945325, 525808751, 515876382, 506143545, 496605696, 487258421, 478097427, 469118539, 460317697, 451690949, 443234452, 434944464, 426817343, 418849541, 411037605, 403378171, 395867960, 388503779, 381282515, 374201134, 367256676, 360446258]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 668).prefactor = (4545855727140201/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 668).cutoff/(generalMeanRows 668).c)).2 =
    (393984718141999/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 668).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 668).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 668).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 668

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 668).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 668).criticalRate j.val*(generalMeanRows 668).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 668).c*(generalMeanRows 668).criticalPoint j.val)).2-
      (generalMeanRows 668).J/2-(generalMeanRows 668).error (generalMeanGrid j.val)+
      (generalMeanRows 668).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 668).c)).2-
      (generalMeanRows 668).J/2-(generalMeanRows 668).error 4 := by
  have he : (generalMeanRows 668).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 668) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 668)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0668

/-! Kernel-checked entropy margins for general spectral rectangle 669. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0669
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5541897390, 5370095887, 5205671086, 5048208921, 4897324397, 4752659053, 4613878686, 4480671329, 4352745434, 4229828232, 4111664264, 3998014047, 3888652865, 3783369674, 3681966105, 3584255549, 3490062335, 3399220959, 3311575394, 3226978445, 3145291161, 3066382293, 2990127792, 2916410349, 2845118964, 2776148553, 2709399580, 2644777715, 2582193520, 2521562154, 2462803099, 2405839905, 2350599950, 2297014224, 2245017116, 2194546222, 2145542164, 2097948421, 2051711170, 2006779136, 1963103455, 1920637540, 1879336959, 1839159321, 1800064165, 1762012861, 1724968510, 1688895859, 1653761209, 1619532341, 1586178438, 1553670012, 1521978839, 1491077897, 1460941300, 1431544250, 1402862976, 1374874689, 1347557529, 1320890526, 1294853552, 1269427284, 1244593163, 1220333361, 1196630743, 1173468839, 1150831809, 1128704415, 1107071996, 1085920439, 1065236152, 1045006047, 1025217512, 1005858391, 986916965, 968381933, 950242389, 932487813, 915108048, 898093285, 881434052, 865121196, 849145869, 833499520, 818173879, 803160944, 788452973, 774042475, 759922193, 746085102, 732524396, 719233479, 706205959, 693435638, 680916505, 668642729, 656608653, 644808786, 633237796, 621890508, 610761893, 599847066, 589141280, 578639920, 568338501, 558232659, 548318151, 538590848, 529046731, 519681890, 510492516, 501474903, 492625439, 483940606, 475416976, 467051207, 458840044, 450780311, 442868913, 435102829, 427479115]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 669).prefactor = (4551830731611471/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 669).cutoff/(generalMeanRows 669).c)).2 =
    (79675186816997/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 669).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 669).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 669).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 669

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 669).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 669).criticalRate j.val*(generalMeanRows 669).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 669).c*(generalMeanRows 669).criticalPoint j.val)).2-
      (generalMeanRows 669).J/2-(generalMeanRows 669).error (generalMeanGrid j.val)+
      (generalMeanRows 669).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 669).c)).2-
      (generalMeanRows 669).J/2-(generalMeanRows 669).error 4 := by
  have he : (generalMeanRows 669).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 669) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 669)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0669

/-! Kernel-checked entropy margins for general spectral rectangle 670. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0670
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5095494538, 4923269259, 4758591192, 4601039096, 4450221140, 4305772340, 4167352264, 4034642986, 3907347249, 3785186813, 3667900965, 3555245174, 3446989872, 3342919343, 3242830719, 3146533056, 3053846501, 2964601515, 2878638176, 2795805527, 2715960981, 2638969775, 2564704464, 2493044450, 2423875554, 2357089615, 2292584119, 2230261852, 2170030586, 2111802775, 2055495284, 2001029126, 1948329227, 1897324195, 1847946115, 1800130353, 1753815370, 1708942550, 1665456044, 1623302613, 1582431490, 1542794248, 1504344673, 1467038647, 1430834040, 1395690604, 1361569879, 1328435094, 1296251089, 1264984229, 1234602326, 1205074570, 1176371457, 1148464729, 1121327306, 1094933236, 1069257634, 1044276636, 1019967345, 996307790, 973276877, 950854352, 929020761, 907757410, 887046332, 866870257, 847212572, 828057301, 809389067, 791193072, 773455068, 756161335, 739298654, 722854288, 706815963, 691171842, 675910510, 661020959, 646492565, 632315074, 618478588, 604973548, 591790723, 578921192, 566356335, 554087822, 542107595, 530407863, 518981091, 507819987, 496917492, 486266777, 475861227, 465694436, 455760199, 446052504, 436565525, 427293613, 418231295, 409373259, 400714356, 392249590, 383974112, 375883218, 367972340, 360237044, 352673023, 345276096, 338042198, 330967383, 324047814, 317279761, 310659600, 304183806, 297848952, 291651702, 285588816, 279657136, 273853592, 268175197, 262619040]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 670).prefactor = (1155171614687949/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 670).cutoff/(generalMeanRows 670).c)).2 =
    (176195410421581/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 670).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 670).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 670).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 670

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 670).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 670).criticalRate j.val*(generalMeanRows 670).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 670).c*(generalMeanRows 670).criticalPoint j.val)).2-
      (generalMeanRows 670).J/2-(generalMeanRows 670).error (generalMeanGrid j.val)+
      (generalMeanRows 670).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 670).c)).2-
      (generalMeanRows 670).J/2-(generalMeanRows 670).error 4 := by
  have he : (generalMeanRows 670).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 670) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 670)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0670

/-! Kernel-checked entropy margins for general spectral rectangle 671. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0671
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5101290695, 4930932365, 4768068475, 4612276797, 4463164748, 4320366805, 4183542189, 4052372808, 3926561397, 3805829856, 3689917745, 3578580924, 3471590324, 3368730822, 3269800231, 3174608363, 3082976185, 2994735039, 2909725932, 2827798882, 2748812314, 2672632505, 2599133077, 2528194522, 2459703764, 2393553756, 2329643108, 2267875735, 2208160536, 2150411093, 2094545393, 2040485568, 1988157650, 1937491344, 1888419823, 1840879521, 1794809958, 1750153558, 1706855495, 1664863537, 1624127902, 1584601132, 1546237959, 1508995193, 1472831612, 1437707853, 1403586320, 1370431086, 1338207815, 1306883670, 1276427246, 1246808490, 1217998638, 1189970145, 1162696632, 1136152819, 1110314481, 1085158386, 1060662257, 1036804718, 1013565254, 990924171, 968862556, 947362240, 926405762, 905976340, 886057835, 866634725, 847692075, 829215511, 811191195, 793605799, 776446487, 759700888, 743357077, 727403560, 711829247, 696623442, 681775824, 667276428, 653115634, 639284151, 625773002, 612573513, 599677300, 587076257, 574762542, 562728572, 550967009, 539470749, 528232917, 517246854, 506506110, 496004436, 485735779, 475694269, 465874214, 456270099, 446876569, 437688433, 428700651, 419908334, 411306731, 402891234, 394657365, 386600773, 378717233, 371002637, 363452993, 356064420, 348833145, 341755496, 334827904, 328046896, 321409092, 314911203, 308550026, 302322445, 296225425, 290256009, 284411318]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 671).prefactor = (4612266828209597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 671).cutoff/(generalMeanRows 671).c)).2 =
    (74216590771063/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 671).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 671).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 671).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 671

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 671).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 671).criticalRate j.val*(generalMeanRows 671).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 671).c*(generalMeanRows 671).criticalPoint j.val)).2-
      (generalMeanRows 671).J/2-(generalMeanRows 671).error (generalMeanGrid j.val)+
      (generalMeanRows 671).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 671).c)).2-
      (generalMeanRows 671).J/2-(generalMeanRows 671).error 4 := by
  have he : (generalMeanRows 671).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 671) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 671)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0671

/-! Kernel-checked entropy margins for general spectral rectangle 672. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0672
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5147720081, 4978125420, 4815992663, 4660899202, 4512452198, 4370285986, 4234059757, 4103455478, 3978176035, 3857943555, 3742497893, 3631595272, 3525007037, 3422518533, 3323928080, 3229046041, 3137693962, 3049703798, 2964917190, 2883184811, 2804365760, 2728327002, 2654942855, 2584094518, 2515669626, 2449561849, 2385670513, 2323900247, 2264160667, 2206366064, 2150435131, 2096290698, 2043859489, 1993071893, 1943861755, 1896166176, 1849925327, 1805082276, 1761582826, 1719375362, 1678410712, 1638642006, 1600024560, 1562515750, 1526074904, 1490663203, 1456243574, 1422780605, 1390240458, 1358590783, 1327800645, 1297840453, 1268681886, 1240297834, 1212662335, 1185750520, 1159538554, 1134003590, 1109123720, 1084877925, 1061246037, 1038208697, 1015747314, 993844030, 972481689, 951643795, 931314493, 911478529, 892121229, 873228470, 854786653, 836782685, 819203951, 802038294, 785273998, 768899762, 752904689, 737278264, 722010339, 707091118, 692511140, 678261267, 664332667, 650716808, 637405437, 624390575, 611664505, 599219757, 587049102, 575145543, 563502304, 552112819, 540970729, 530069871, 519404269, 508968131, 498755839, 488761941, 478981150, 469408332, 460038505, 450866830, 441888610, 433099279, 424494402, 416069670, 407820893, 399743998, 391835024, 384090117, 376505532, 369077621, 361802835, 354677720, 347698913, 340863140, 334167211, 327608022, 321182544, 314887831, 308721008]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 672).prefactor = (460805775338637/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 672).cutoff/(generalMeanRows 672).c)).2 =
    (38429256538203/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 672).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 672).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 672).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 672

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 672).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 672).criticalRate j.val*(generalMeanRows 672).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 672).c*(generalMeanRows 672).criticalPoint j.val)).2-
      (generalMeanRows 672).J/2-(generalMeanRows 672).error (generalMeanGrid j.val)+
      (generalMeanRows 672).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 672).c)).2-
      (generalMeanRows 672).J/2-(generalMeanRows 672).error 4 := by
  have he : (generalMeanRows 672).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 672) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 672)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0672

/-! Kernel-checked entropy margins for general spectral rectangle 673. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0673
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5015616505, 4845657851, 4683232587, 4527914710, 4379308173, 4237044270, 4100779304, 3970192500, 3844984135, 3724873850, 3609599133, 3498913942, 3392587463, 3290402974, 3192156818, 3097657464, 3006724644, 2919188571, 2834889218, 2753675656, 2675405441, 2599944060, 2527164411, 2456946322, 2389176114, 2323746191, 2260554659, 2199504977, 2140505626, 2083469813, 2028315181, 1974963549, 1923340668, 1873375991, 1825002457, 1778156297, 1732776841, 1688806348, 1646189841, 1604874954, 1564811788, 1525952778, 1488252564, 1451667875, 1416157414, 1381681758, 1348203256, 1315685938, 1284095427, 1253398855, 1223564789, 1194563158, 1166365179, 1138943299, 1112271129, 1086323387, 1061075845, 1036505277, 1012589410, 989306875, 966637168, 944560608, 923058295, 902112075, 881704505, 861818821, 842438904, 823549253, 805134955, 787181657, 769675545, 752603317, 735952159, 719709727, 703864121, 688403873, 673317920, 658595594, 644226599, 630201000, 616509203, 603141945, 590090279, 577345559, 564899428, 552743810, 540870892, 529273121, 517943185, 506874013, 496058757, 485490787, 475163685, 465071230, 455207398, 445566348, 436142422, 426930129, 417924149, 409119318, 400510626, 392093214, 383862363, 375813493, 367942156, 360244033, 352714927, 345350760, 338147573, 331101512, 324208835, 317465902, 310869173, 304415205, 298100648, 291922243, 285876819, 279961289, 274172648, 268507970, 262964406]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 673).prefactor = (4641029936910341/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 673).cutoff/(generalMeanRows 673).c)).2 =
    (46149742394943/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 673).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 673).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 673).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 673

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 673).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 673).criticalRate j.val*(generalMeanRows 673).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 673).c*(generalMeanRows 673).criticalPoint j.val)).2-
      (generalMeanRows 673).J/2-(generalMeanRows 673).error (generalMeanGrid j.val)+
      (generalMeanRows 673).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 673).c)).2-
      (generalMeanRows 673).J/2-(generalMeanRows 673).error 4 := by
  have he : (generalMeanRows 673).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 673) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 673)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0673

/-! Kernel-checked entropy margins for general spectral rectangle 674. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0674
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5054639484, 4883486903, 4719892108, 4563429592, 4413703699, 4270346013, 4133013037, 4001384116, 3875159566, 3754059004, 3637819830, 3526195859, 3418956084, 3315883545, 3216774309, 3121436531, 3029689601, 2941363361, 2856297390, 2774340345, 2695349352, 2619189451, 2545733083, 2474859608, 2406454875, 2340410806, 2276625024, 2215000501, 2155445233, 2097871940, 2042197780, 1988344093, 1936236150, 1885802931, 1836976908, 1789693848, 1743892627, 1699515056, 1656505717, 1614811809, 1574383011, 1535171338, 1497131025, 1460218399, 1424391776, 1389611350, 1355839100, 1323038691, 1291175392, 1260215992, 1230128723, 1200883186, 1172450282, 1144802149, 1117912098, 1091754556, 1066305014, 1041539970, 1017436886, 993974135, 971130965, 948887451, 927224460, 906123611, 885567242, 865538376, 846020689, 826998482, 808456648, 790380652, 772756500, 755570715, 738810317, 722462801, 706516112, 690958630, 675779149, 660966859, 646511331, 632402499, 618630644, 605186383, 592060651, 579244690, 566730036, 554508508, 542572193, 530913440, 519524847, 508399251, 497529718, 486909537, 476532206, 466391432, 456481114, 446795342, 437328386, 428074693, 419028877, 410185715, 401540138, 393087230, 384822218, 376740470, 368837489, 361108906, 353550479, 346158087, 338927724, 331855500, 324937631, 318170439, 311550347, 305073879, 298737651, 292538370, 286472836, 280537931, 274730622, 269047956, 263487056]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 674).prefactor = (4645835326412733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 674).cutoff/(generalMeanRows 674).c)).2 =
    (45445515180161/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 674).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 674).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 674).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 674

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 674).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 674).criticalRate j.val*(generalMeanRows 674).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 674).c*(generalMeanRows 674).criticalPoint j.val)).2-
      (generalMeanRows 674).J/2-(generalMeanRows 674).error (generalMeanGrid j.val)+
      (generalMeanRows 674).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 674).c)).2-
      (generalMeanRows 674).J/2-(generalMeanRows 674).error 4 := by
  have he : (generalMeanRows 674).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 674) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 674)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0674

/-! Kernel-checked entropy margins for general spectral rectangle 675. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0675
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4928059400, 4756652868, 4592875323, 4436297679, 4286520894, 4143173348, 4005908509, 3874402837, 3748353914, 3627478751, 3511512268, 3400205918, 3293326438, 3190654719, 3091984770, 2997122783, 2905886267, 2818103267, 2733611638, 2652258386, 2573899056, 2498397172, 2425623718, 2355456660, 2287780505, 2222485889, 2159469200, 2098632224, 2039881817, 1983129603, 1928291689, 1875288402, 1824044043, 1774486656, 1726547816, 1680162428, 1635268539, 1591807160, 1549722110, 1508959851, 1469469353, 1431201955, 1394111235, 1358152895, 1323284649, 1289466113, 1256658708, 1224825569, 1193931453, 1163942659, 1134826948, 1106553469, 1079092691, 1052416339, 1026497325, 1001309700, 976828587, 953030140, 929891485, 907390680, 885506668, 864219234, 843508968, 823357227, 803746096, 784658359, 766077465, 747987498, 730373145, 713219675, 696512910, 680239197, 664385390, 648938826, 633887303, 619219062, 604922763, 590987476, 577402652, 564158119, 551244057, 538650986, 526369754, 514391523, 502707751, 491310188, 480190859, 469342053, 458756316, 448426435, 438345436, 428506567, 418903295, 409529296, 400378444, 391444809, 382722644, 374206381, 365890626, 357770149, 349839879, 342094899, 334530440, 327141877, 319924720, 312874614, 305987331, 299258766, 292684934, 286261964, 279986098, 273853682, 267861168, 262005109, 256282151, 250689038, 245222601, 239879759, 234657517, 229552961, 224563256]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 675).prefactor = (2339824069602121/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 675).cutoff/(generalMeanRows 675).c)).2 =
    (87173489740459/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 675).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 675).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 675).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 675

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 675).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 675).criticalRate j.val*(generalMeanRows 675).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 675).c*(generalMeanRows 675).criticalPoint j.val)).2-
      (generalMeanRows 675).J/2-(generalMeanRows 675).error (generalMeanGrid j.val)+
      (generalMeanRows 675).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 675).c)).2-
      (generalMeanRows 675).J/2-(generalMeanRows 675).error 4 := by
  have he : (generalMeanRows 675).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 675) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 675)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0675

/-! Kernel-checked entropy margins for general spectral rectangle 676. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0676
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5275917600, 5107003492, 4945421981, 4790759850, 4642632954, 4500683675, 4364578660, 4234006792, 4108677374, 3988318490, 3872675534, 3761509872, 3654597636, 3551728626, 3452705308, 3357341904, 3265463563, 3176905593, 3091512763, 3009138667, 2929645125, 2852901647, 2778784926, 2707178379, 2637971717, 2571060546, 2506346005, 2443734421, 2383136993, 2324469499, 2267652021, 2212608691, 2159267451, 2107559833, 2057420752, 2008788312, 1961603622, 1915810635, 1871355978, 1828188814, 1786260697, 1745525441, 1705939000, 1667459354, 1630046395, 1593661834, 1558269095, 1523833234, 1490320852, 1457700010, 1425940162, 1395012077, 1364887779, 1335540477, 1306944510, 1279075290, 1251909251, 1225423792, 1199597238, 1174408792, 1149838489, 1125867164, 1102476406, 1079648527, 1057366526, 1035614060, 1014375409, 993635450, 973379628, 953593933, 934264873, 915379449, 896925139, 878889869, 861262000, 844030305, 827183951, 810712484, 794605813, 778854192, 763448207, 748378759, 733637059, 719214604, 705103174, 691294816, 677781834, 664556780, 651612441, 638941834, 626538192, 614394960, 602505783, 590864500, 579465138, 568301902, 557369169, 546661484, 536173551, 525900226, 515836515, 505977568, 496318671, 486855242, 477582830, 468497104, 459593854, 450868985, 442318513, 433938561, 425725355, 417675222, 409784586, 402049962, 394467959, 387035272, 379748679, 372605043, 365601304, 358734479, 352001660]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 676).prefactor = (56877118253863/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 676).cutoff/(generalMeanRows 676).c)).2 =
    (78094993058069/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 676).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 676).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 676).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 676

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 676).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 676).criticalRate j.val*(generalMeanRows 676).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 676).c*(generalMeanRows 676).criticalPoint j.val)).2-
      (generalMeanRows 676).J/2-(generalMeanRows 676).error (generalMeanGrid j.val)+
      (generalMeanRows 676).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 676).c)).2-
      (generalMeanRows 676).J/2-(generalMeanRows 676).error 4 := by
  have he : (generalMeanRows 676).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 676) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 676)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0676

/-! Kernel-checked entropy margins for general spectral rectangle 677. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0677
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5012290221, 4842507771, 4680203237, 4524956605, 4376377297, 4234101599, 4097790374, 3967127009, 3841815576, 3721579177, 3606158456, 3495310242, 3388806334, 3286432388, 3187986903, 3093280304, 3002134094, 2914380089, 2829859709, 2748423324, 2669929665, 2594245268, 2521243968, 2450806431, 2382819723, 2317176904, 2253776658, 2192522951, 2133324707, 2076095511, 2020753330, 1967220260, 1915422280, 1865289028, 1816753592, 1769752317, 1724224615, 1680112799, 1637361920, 1595919615, 1555735971, 1516763386, 1478956448, 1442271818, 1406668121, 1372105840, 1338547222, 1305956184, 1274298229, 1243540364, 1213651023, 1184599996, 1156358359, 1128898414, 1102193625, 1076218560, 1050948840, 1026361087, 1002432874, 979142682, 956469855, 934394558, 912897742, 891961104, 871567055, 851698683, 832339727, 813474544, 795088080, 777165849, 759693900, 742658800, 726047606, 709847847, 694047502, 678634981, 663599105, 648929090, 634614528, 620645377, 607011937, 593704842, 580715044, 568033801, 555652662, 543563460, 531758293, 520229522, 508969754, 497971835, 487228841, 476734067, 466481022, 456463415, 446675154, 437110334, 427763233, 418628301, 409700157, 400973583, 392443515, 384105041, 375953392, 367983941, 360192193, 352573784, 345124477, 337840152, 330716810, 323750563, 316937630, 310274337, 303757113, 297382483, 291147068, 285047579, 279080820, 273243677, 267533120, 261946201, 256480049]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 677).prefactor = (923300877508277/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 677).cutoff/(generalMeanRows 677).c)).2 =
    (360510176588411/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 677).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 677).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 677).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 677

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 677).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 677).criticalRate j.val*(generalMeanRows 677).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 677).c*(generalMeanRows 677).criticalPoint j.val)).2-
      (generalMeanRows 677).J/2-(generalMeanRows 677).error (generalMeanGrid j.val)+
      (generalMeanRows 677).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 677).c)).2-
      (generalMeanRows 677).J/2-(generalMeanRows 677).error 4 := by
  have he : (generalMeanRows 677).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 677) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 677)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0677

/-! Kernel-checked entropy margins for general spectral rectangle 678. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0678
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4969174948, 4798476542, 4635373799, 4479437445, 4330268362, 4187494962, 4050770834, 3919772649, 3794198270, 3673765061, 3558208356, 3447280076, 3340747474, 3238391999, 3140008256, 3045403061, 2954394579, 2866811530, 2782492466, 2701285103, 2623045710, 2547638544, 2474935327, 2404814770, 2337162123, 2271868768, 2208831836, 2147953849, 2089142399, 2032309837, 1977372987, 1924252888, 1872874539, 1823166677, 1775061553, 1728494738, 1683404932, 1639733788, 1597425751, 1556427897, 1516689795, 1478163369, 1440802767, 1404564249, 1369406069, 1335288370, 1302173088, 1270023853, 1238805908, 1208486021, 1179032407, 1150414658, 1122603671, 1095571582, 1069291707, 1043738480, 1018887403, 994714987, 971198710, 948316964, 926049018, 904374970, 883275711, 862732886, 842728861, 823246688, 804270074, 785783348, 767771438, 750219840, 733114592, 716442254, 700189879, 684344996, 668895587, 653830066, 639137264, 624806408, 610827104, 597189322, 583883383, 570899937, 558229959, 545864726, 533795812, 522015073, 510514634, 499286881, 488324447, 477620208, 467167268, 456958951, 446988794, 437250539, 427738124, 418445674, 409367498, 400498078, 391832065, 383364272, 375089669, 367003374, 359100652, 351376907, 343827677, 336448630, 329235561, 322184384, 315291129, 308551942, 301963074, 295520884, 289221831, 283062472, 277039459, 271149537, 265389537, 259756379, 254247064, 248858673, 243588366]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 678).prefactor = (467423804735721/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 678).cutoff/(generalMeanRows 678).c)).2 =
    (361735217957953/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 678).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 678).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 678).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 678

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 678).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 678).criticalRate j.val*(generalMeanRows 678).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 678).c*(generalMeanRows 678).criticalPoint j.val)).2-
      (generalMeanRows 678).J/2-(generalMeanRows 678).error (generalMeanGrid j.val)+
      (generalMeanRows 678).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 678).c)).2-
      (generalMeanRows 678).J/2-(generalMeanRows 678).error 4 := by
  have he : (generalMeanRows 678).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 678) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 678)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0678

/-! Kernel-checked entropy margins for general spectral rectangle 679. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0679
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5031702171, 4861141037, 4698154137, 4542312208, 4393216209, 4250494685, 4113801413, 3982813296, 3857228477, 3736764634, 3621157447, 3510159217, 3403537599, 3301074467, 3202564870, 3107816086, 3016646753, 2928886077, 2844373104, 2762956050, 2684491692, 2608844793, 2535887589, 2465499299, 2397565685, 2331978636, 2268635787, 2207440162, 2148299847, 2091127682, 2035840975, 1982361241, 1930613948, 1880528292, 1832036977, 1785076017, 1739584547, 1695504644, 1652781169, 1611361603, 1571195912, 1532236405, 1494437608, 1457756146, 1422150630, 1387581548, 1354011174, 1321403465, 1289723979, 1258939792, 1229019418, 1199932735, 1171650919, 1144146377, 1117392683, 1091364526, 1066037646, 1041388792, 1017395665, 994036877, 971291904, 949141045, 927565385, 906546756, 886067701, 866111444, 846661855, 827703421, 809221220, 791200893, 773628615, 756491077, 739775457, 723469405, 707561015, 692038812, 676891727, 662109086, 647680588, 633596291, 619846597, 606422238, 593314260, 580514011, 568013131, 555803536, 543877410, 532227192, 520845566, 509725455, 498860004, 488242579, 477866754, 467726305, 457815199, 448127591, 438657815, 429400375, 420349943, 411501349, 402849578, 394389763, 386117178, 378027237, 370115485, 362377594, 354809363, 347406707, 340165657, 333082355, 326153051, 319374096, 312741944, 306253145, 299904342, 293692269, 287613746, 281665680, 275845058, 270148949, 264574494]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 679).prefactor = (2335771562482041/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 679).cutoff/(generalMeanRows 679).c)).2 =
    (18601339768001/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 679).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 679).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 679).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 679

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 679).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 679).criticalRate j.val*(generalMeanRows 679).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 679).c*(generalMeanRows 679).criticalPoint j.val)).2-
      (generalMeanRows 679).J/2-(generalMeanRows 679).error (generalMeanGrid j.val)+
      (generalMeanRows 679).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 679).c)).2-
      (generalMeanRows 679).J/2-(generalMeanRows 679).error 4 := by
  have he : (generalMeanRows 679).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 679) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 679)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0679

/-! Kernel-checked entropy margins for general spectral rectangle 680. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0680
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4967020012, 4796330705, 4633250859, 4477349471, 4328225853, 4185506993, 4048845189, 3917915942, 3792416058, 3672061946, 3556588076, 3445745594, 3339301052, 3237035272, 3138742298, 3044228442, 2953311422, 2865819560, 2781591056, 2700473316, 2622322335, 2547002132, 2474384224, 2404347142, 2336775985, 2271562008, 2208602233, 2147799098, 2089060123, 2032297605, 1977428330, 1924373310, 1873057530, 1823409720, 1775362138, 1728850368, 1683813128, 1640192101, 1597931761, 1556979223, 1517284098, 1478798353, 1441476188, 1405273912, 1370149832, 1336064148, 1302978850, 1270857630, 1239665785, 1209370144, 1179938983, 1151341951, 1123550006, 1096535344, 1070271337, 1044732480, 1019894329, 995733455, 972227390, 949354581, 927094351, 905426850, 884333020, 863794557, 843793876, 824314077, 805338911, 786852755, 768840580, 751287923, 734180866, 717506006, 701250436, 685401722, 669947882, 654877365, 640179036, 625842152, 611856353, 598211639, 584898357, 571907187, 559229129, 546855488, 534777860, 522988125, 511478432, 500241186, 489269043, 478554897, 468091870, 457873307, 447892760, 438143987, 428620942, 419317766, 410228780, 401348481, 392671532, 384192758, 375907139, 367809807, 359896035, 352161237, 344600960, 337210881, 329986803, 322924647, 316020453, 309270370, 302670657, 296217679, 289907901, 283737884, 277704286, 271803855, 266033428, 260389928, 254870359, 249471806, 244191432]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 680).prefactor = (586010855869279/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 680).cutoff/(generalMeanRows 680).c)).2 =
    (364564074158431/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 680).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 680).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 680).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 680

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 680).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 680).criticalRate j.val*(generalMeanRows 680).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 680).c*(generalMeanRows 680).criticalPoint j.val)).2-
      (generalMeanRows 680).J/2-(generalMeanRows 680).error (generalMeanGrid j.val)+
      (generalMeanRows 680).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 680).c)).2-
      (generalMeanRows 680).J/2-(generalMeanRows 680).error 4 := by
  have he : (generalMeanRows 680).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 680) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 680)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0680

/-! Kernel-checked entropy margins for general spectral rectangle 681. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0681
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4986921308, 4815613289, 4651928059, 4495434810, 4345733002, 4202449716, 4065237308, 3933771290, 3807748448, 3686885137, 3570915746, 3459591309, 3352678249, 3249957233, 3151222133, 3056279076, 2964945576, 2877049742, 2792429550, 2710932173, 2632413365, 2556736897, 2483774036, 2413403058, 2345508804, 2279982268, 2216720212, 2155624813, 2096603331, 2039567802, 1984434757, 1931124951, 1879563116, 1829677732, 1781400811, 1734667692, 1689416857, 1645589752, 1603130620, 1561986351, 1522106333, 1483442317, 1445948290, 1409580354, 1374296614, 1340057071, 1306823524, 1274559475, 1243230042, 1212801874, 1183243072, 1154523121, 1126612813, 1099484185, 1073110456, 1047465972, 1022526144, 998267402, 974667141, 951703678, 929356207, 907604754, 886430143, 865813954, 845738489, 826186740, 807142355, 788589608, 770513372, 752899092, 735732756, 719000876, 702690460, 686788990, 671284406, 656165082, 641419808, 627037772, 613008544, 599322058, 585968599, 572938786, 560223559, 547814167, 535702151, 523879340, 512337829, 501069978, 490068395, 479325928, 468835657, 458590883, 448585120, 438812087, 429265700, 419940064, 410829467, 401928372, 393231410, 384733377, 376429223, 368314049, 360383105, 352631775, 345055585, 337650186, 330411356, 323334997, 316417125, 309653870, 303041472, 296576275, 290254726, 284073370, 278028847, 272117890, 266337320, 260684044, 255155053, 249747419, 244458290]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 681).prefactor = (586366387781031/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 681).cutoff/(generalMeanRows 681).c)).2 =
    (361735217957953/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 681).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 681).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 681).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 681

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 681).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 681).criticalRate j.val*(generalMeanRows 681).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 681).c*(generalMeanRows 681).criticalPoint j.val)).2-
      (generalMeanRows 681).J/2-(generalMeanRows 681).error (generalMeanGrid j.val)+
      (generalMeanRows 681).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 681).c)).2-
      (generalMeanRows 681).J/2-(generalMeanRows 681).error 4 := by
  have he : (generalMeanRows 681).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 681) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 681)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0681

/-! Kernel-checked entropy margins for general spectral rectangle 682. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0682
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4923596001, 4752186446, 4588434801, 4431908473, 4282205233, 4138950567, 4001795313, 3870413548, 3744500691, 3623771799, 3507960024, 3396815221, 3290102689, 3187602023, 3089106068, 2994419974, 2903360316, 2815754309, 2731439067, 2650260943, 2572074902, 2496743962, 2424138663, 2354136587, 2286621909, 2221484982, 2158621954, 2097934412, 2039329051, 1982717362, 1928015354, 1875143279, 1824025389, 1774589699, 1726767777, 1680494535, 1635708044, 1592349355, 1550362334, 1509693506, 1470291910, 1432108961, 1395098324, 1359215793, 1324419176, 1290668189, 1257924358, 1226150924, 1195312753, 1165376254, 1136309298, 1108081148, 1080662385, 1054024844, 1028141551, 1002986664, 978535420, 954764078, 931649873, 909170967, 887306407, 866036078, 845340672, 825201640, 805601164, 786522121, 767948049, 749863120, 732252107, 715100362, 698393787, 682118807, 666262354, 650811836, 635755122, 621080522, 606776763, 592832976, 579238678, 565983752, 553058436, 540453307, 528159265, 516167521, 504469584, 493057249, 481922587, 471057929, 460455862, 450109214, 440011047, 430154646, 420533512, 411141353, 401972076, 393019779, 384278744, 375743432, 367408471, 359268658, 351318944, 343554435, 335970383, 328562181, 321325360, 314255581, 307348633, 300600427, 294006993, 287564474, 281269125, 275117304, 269105476, 263230202, 257488142, 251876046, 246390755, 241029198, 235788386, 230665411, 225657447]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 682).prefactor = (4707683772862483/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 682).cutoff/(generalMeanRows 682).c)).2 =
    (35432777668009/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 682).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 682).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 682).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 682

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 682).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 682).criticalRate j.val*(generalMeanRows 682).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 682).c*(generalMeanRows 682).criticalPoint j.val)).2-
      (generalMeanRows 682).J/2-(generalMeanRows 682).error (generalMeanGrid j.val)+
      (generalMeanRows 682).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 682).c)).2-
      (generalMeanRows 682).J/2-(generalMeanRows 682).error 4 := by
  have he : (generalMeanRows 682).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 682) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 682)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0682

/-! Kernel-checked entropy margins for general spectral rectangle 683. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0683
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5236997194, 5069212918, 4908765844, 4755238816, 4608244169, 4467421154, 4332433638, 4202968049, 4078731528, 3959450267, 3844868013, 3734744711, 3628855274, 3526988469, 3428945897, 3334541073, 3243598571, 3155953253, 3071449558, 2989940848, 2911288808, 2835362893, 2762039818, 2691203085, 2622742552, 2556554026, 2492538891, 2430603760, 2370660157, 2312624215, 2256416396, 2201961237, 2149187105, 2098025973, 2048413211, 2000287388, 1953590087, 1908265741, 1864261461, 1821526898, 1780014092, 1739677345, 1700473098, 1662359811, 1625297856, 1589249414, 1554178381, 1520050272, 1486832141, 1454492498, 1423001232, 1392329546, 1362449881, 1333335860, 1304962225, 1277304781, 1250340345, 1224046692, 1198402510, 1173387357, 1148981613, 1125166448, 1101923777, 1079236228, 1057087108, 1035460369, 1014340580, 993712897, 973563036, 953877247, 934642291, 915845415, 897474330, 879517192, 861962581, 844799482, 828017268, 811605683, 795554824, 779855128, 764497359, 749472590, 734772191, 720387820, 706311407, 692535144, 679051476, 665853089, 652932900, 640284048, 627899887, 615773974, 603900066, 592272106, 580884222, 569730715, 558806056, 548104877, 537621967, 527352265, 517290854, 507432958, 497773934, 488309270, 479034577, 469945589, 461038154, 452308235, 443751902, 435365328, 427144790, 419086662, 411187412, 403443599, 395851873, 388408966, 381111695, 373956956, 366941725, 360063050, 353318053]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 683).prefactor = (4573310984456263/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 683).cutoff/(generalMeanRows 683).c)).2 =
    (401648265888471/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 683).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 683).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 683).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 683

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 683).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 683).criticalRate j.val*(generalMeanRows 683).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 683).c*(generalMeanRows 683).criticalPoint j.val)).2-
      (generalMeanRows 683).J/2-(generalMeanRows 683).error (generalMeanGrid j.val)+
      (generalMeanRows 683).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 683).c)).2-
      (generalMeanRows 683).J/2-(generalMeanRows 683).error 4 := by
  have he : (generalMeanRows 683).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 683) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 683)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0683

/-! Kernel-checked entropy margins for general spectral rectangle 684. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0684
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5100795176, 4932546186, 4771706050, 4617854378, 4470600442, 4329580588, 4194455926, 4064910256, 3940648220, 3821393625, 3706887941, 3596888937, 3491169444, 3389516235, 3291729001, 3197619424, 3107010318, 3019734856, 2935635854, 2854565113, 2776382813, 2700956966, 2628162892, 2557882753, 2490005114, 2424424535, 2361041198, 2299760557, 2240493017, 2183153630, 2127661818, 2073941111, 2021918905, 1971526234, 1922697563, 1875370585, 1829486041, 1784987542, 1741821416, 1699936549, 1659284246, 1619818099, 1581493861, 1544269329, 1508104235, 1472960143, 1438800348, 1405589792, 1373294969, 1341883852, 1311325814, 1281591553, 1252653030, 1224483400, 1197056957, 1170349072, 1144336142, 1118995541, 1094305568, 1070245406, 1046795077, 1023935402, 1001647963, 979915065, 958719707, 938045544, 917876858, 898198530, 878996014, 860255305, 841962921, 824105875, 806671656, 789648205, 773023897, 756787519, 740928258, 725435677, 710299701, 695510605, 681058995, 666935794, 653132233, 639639832, 626450394, 613555990, 600948947, 588621842, 576567489, 564778929, 553249423, 541972441, 530941658, 520150940, 509594343, 499266102, 489160622, 479272480, 469596409, 460127298, 450860185, 441790250, 432912814, 424223328, 415717374, 407390657, 399239000, 391258344, 383444740, 375794348, 368303431, 360968353, 353785574, 346751649, 339863225, 333117034, 326509896, 320038711, 313700461, 307492204, 301411071]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 684).prefactor = (4605415871233103/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 684).cutoff/(generalMeanRows 684).c)).2 =
    (77310727933197/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 684).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 684).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 684).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 684

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 684).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 684).criticalRate j.val*(generalMeanRows 684).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 684).c*(generalMeanRows 684).criticalPoint j.val)).2-
      (generalMeanRows 684).J/2-(generalMeanRows 684).error (generalMeanGrid j.val)+
      (generalMeanRows 684).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 684).c)).2-
      (generalMeanRows 684).J/2-(generalMeanRows 684).error 4 := by
  have he : (generalMeanRows 684).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 684) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 684)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0684

/-! Kernel-checked entropy margins for general spectral rectangle 685. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0685
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4984610131, 4813316348, 4649658974, 4493205479, 4343553757, 4200329475, 4063183699, 3931790782, 3805846455, 3685066122, 3569183316, 3457948297, 3351126795, 3248498853, 3149857785, 3055009220, 2963770228, 2875968524, 2791441734, 2710036725, 2631608982, 2556022041, 2483146965, 2412861855, 2345051403, 2279606479, 2216423739, 2155405277, 2096458284, 2039494748, 1984431161, 1931188252, 1879690744, 1829867112, 1781649375, 1734972888, 1689776155, 1646000649, 1603590649, 1562493083, 1522657382, 1484035344, 1446581007, 1410250525, 1375002057, 1340795662, 1307593197, 1275358223, 1244055916, 1213652987, 1184117598, 1155419294, 1127528927, 1100418595, 1074061577, 1048432277, 1023506165, 999259728, 975670419, 952716609, 930377547, 908633313, 887464781, 866853584, 846782073, 827233288, 808190924, 789639302, 771563339, 753948521, 736780881, 720046969, 703733832, 687828992, 672320423, 657196536, 642446154, 628058499, 614023171, 600330135, 586969706, 573932529, 561209574, 548792112, 536671713, 524840226, 513289772, 502012731, 491001732, 480249643, 469749563, 459494811, 449478919, 439695623, 430138853, 420802731, 411681557, 402769809, 394062132, 385553331, 377238371, 369112362, 361170564, 353408374, 345821324, 338405074, 331155413, 324068247, 317139602, 310365615, 303742530, 297266700, 290934576, 284742708, 278687743, 272766416, 266975554, 261312068, 255772952, 250355281, 245056208]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 685).prefactor = (470468915659517/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 685).cutoff/(generalMeanRows 685).c)).2 =
    (364564074158431/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 685).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 685).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 685).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 685

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 685).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 685).criticalRate j.val*(generalMeanRows 685).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 685).c*(generalMeanRows 685).criticalPoint j.val)).2-
      (generalMeanRows 685).J/2-(generalMeanRows 685).error (generalMeanGrid j.val)+
      (generalMeanRows 685).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 685).c)).2-
      (generalMeanRows 685).J/2-(generalMeanRows 685).error 4 := by
  have he : (generalMeanRows 685).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 685) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 685)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0685

/-! Kernel-checked entropy margins for general spectral rectangle 686. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0686
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4920964480, 4749573896, 4585854694, 4429372571, 4279723741, 4136532281, 3999447752, 3868143075, 3742312623, 3621670507, 3505949028, 3394897274, 3288279855, 3185875745, 3087477238, 2992888987, 2901927128, 2814418484, 2730199825, 2649117197, 2571025301, 2495786920, 2423272395, 2353359133, 2285931163, 2220878714, 2158097832, 2097490022, 2038961910, 1982424940, 1927795084, 1874992570, 1823941639, 1774570306, 1726810143, 1680596081, 1635866213, 1592561617, 1550626197, 1510006514, 1470651654, 1432513078, 1395544501, 1359701771, 1324942750, 1291227211, 1258516741, 1226774637, 1195965826, 1166056778, 1137015425, 1108811091, 1081414416, 1054797298, 1028932821, 1003795203, 979359740, 955602747, 932501516, 910034267, 888180098, 866918951, 846231567, 826099450, 806504832, 787430637, 768860451, 750778491, 733169576, 716019101, 699313007, 683037764, 667180339, 651728181, 636669194, 621991723, 607684530, 593736780, 580138018, 566878161, 553947476, 541336566, 529036359, 517038093, 505333300, 493913801, 482771688, 471899316, 461289292, 450934463, 440827911, 430962939, 421333066, 411932016, 402753713, 393792269, 385041981, 376497322, 368152937, 360003631, 352044369, 344270268, 336676589, 329258738, 322012252, 314932804, 308016189, 301258327, 294655256, 288203125, 281898195, 275736832, 269715506, 263830783, 258079329, 252457897, 246963335, 241592574, 236342630, 231210598, 226193655]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 686).prefactor = (23606751306841/5000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 686).cutoff/(generalMeanRows 686).c)).2 =
    (357156632880569/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 686).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 686).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 686).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 686

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 686).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 686).criticalRate j.val*(generalMeanRows 686).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 686).c*(generalMeanRows 686).criticalPoint j.val)).2-
      (generalMeanRows 686).J/2-(generalMeanRows 686).error (generalMeanGrid j.val)+
      (generalMeanRows 686).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 686).c)).2-
      (generalMeanRows 686).J/2-(generalMeanRows 686).error 4 := by
  have he : (generalMeanRows 686).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 686) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 686)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0686

/-! Kernel-checked entropy margins for general spectral rectangle 687. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0687
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5305679699, 5138210492, 4978067473, 4824831728, 4678114067, 4537552425, 4402809542, 4273570896, 4149542832, 4030450892, 3916038305, 3806064610, 3700304428, 3598546324, 3500591792, 3406254309, 3315358489, 3227739293, 3143241319, 3061718135, 2983031679, 2907051696, 2833655227, 2762726133, 2694154654, 2627837003, 2563674988, 2501575666, 2441451015, 2383217634, 2326796462, 2272112517, 2219094653, 2167675334, 2117790419, 2069378971, 2022383063, 1976747614, 1932420224, 1889351020, 1847492521, 1806799499, 1767228856, 1728739509, 1691292281, 1654849794, 1619376374, 1584837964, 1551202031, 1518437492, 1486514636, 1455405050, 1425081557, 1395518148, 1366689925, 1338573043, 1311144658, 1284382878, 1258266713, 1232776032, 1207891519, 1183594637, 1159867586, 1136693270, 1114055262, 1091937774, 1070325624, 1049204208, 1028559477, 1008377905, 988646469, 969352626, 950484290, 932029809, 913977952, 896317882, 879039146, 862131654, 845585663, 829391763, 813540865, 798024181, 782833220, 767959766, 753395874, 739133854, 725166264, 711485898, 698085775, 684959133, 672099419, 659500279, 647155555, 635059269, 623205626, 611588999, 600203927, 589045106, 578107387, 567385766, 556875380, 546571503, 536469540, 526565023, 516853606, 507331060, 497993271, 488836233, 479856047, 471048916, 462411143, 453939123, 445629347, 437478395, 429482930, 421639703, 413945543, 406397358, 398992133, 391726924, 384598860]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 687).prefactor = (1466921130169/320000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 687).cutoff/(generalMeanRows 687).c)).2 =
    (82983141692359/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 687).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 687).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 687).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 687

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 687).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 687).criticalRate j.val*(generalMeanRows 687).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 687).c*(generalMeanRows 687).criticalPoint j.val)).2-
      (generalMeanRows 687).J/2-(generalMeanRows 687).error (generalMeanGrid j.val)+
      (generalMeanRows 687).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 687).c)).2-
      (generalMeanRows 687).J/2-(generalMeanRows 687).error 4 := by
  have he : (generalMeanRows 687).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 687) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 687)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0687

/-! Kernel-checked entropy margins for general spectral rectangle 688. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0688
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5234867497, 5067118971, 4906732573, 4753287844, 4606394127, 4465687966, 4330830779, 4201506781, 4077421120, 3958298190, 3843880121, 3733925407, 3628207662, 3526514490, 3428646456, 3334416154, 3243647342, 3156174161, 3071840417, 2990498918, 2912010869, 2836245307, 2763078593, 2692393929, 2624080918, 2558035160, 2494157872, 2432355537, 2372539580, 2314626064, 2258535410, 2204192137, 2151524614, 2100464835, 2050948209, 2002913356, 1956301927, 1911058431, 1867130067, 1824466581, 1783020115, 1742745083, 1703598037, 1665537556, 1628524135, 1592520081, 1557489412, 1523397775, 1490212350, 1457901776, 1426436072, 1395786568, 1365925833, 1336827615, 1308466782, 1280819261, 1253861989, 1227572861, 1201930680, 1176915119, 1152506669, 1128686609, 1105436960, 1082740454, 1060580497, 1038941140, 1017807046, 997163463, 976996197, 957291585, 938036469, 919218177, 900824500, 882843667, 865264331, 848075547, 831266755, 814827762, 798748730, 783020154, 767632855, 752577960, 737846893, 723431362, 709323344, 695515079, 681999055, 668767998, 655814868, 643132841, 630715307, 618555859, 606648285, 594986561, 583564843, 572377462, 561418915, 550683859, 540167108, 529863622, 519768508, 509877007, 500184497, 490686483, 481378595, 472256580, 463316302, 454553738, 445964969, 437546184, 429293668, 421203806, 413273077, 405498048, 397875377, 390401804, 383074153, 375889327, 368844305, 361936144, 355161968]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 688).prefactor = (2299962763470001/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 688).cutoff/(generalMeanRows 688).c)).2 =
    (203641041803363/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 688).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 688).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 688).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 688

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 688).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 688).criticalRate j.val*(generalMeanRows 688).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 688).c*(generalMeanRows 688).criticalPoint j.val)).2-
      (generalMeanRows 688).J/2-(generalMeanRows 688).error (generalMeanGrid j.val)+
      (generalMeanRows 688).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 688).c)).2-
      (generalMeanRows 688).J/2-(generalMeanRows 688).error 4 := by
  have he : (generalMeanRows 688).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 688) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 688)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0688

/-! Kernel-checked entropy margins for general spectral rectangle 689. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0689
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5304550411, 5137114629, 4977016676, 4823836017, 4677181997, 4536691224, 4402025244, 4272868455, 4148926234, 4029923250, 3915601949, 3805721173, 3700054913, 3598391181, 3500530974, 3406287331, 3315484481, 3227957046, 3143549326, 3062114633, 2983514683, 2907619032, 2834304562, 2763454998, 2694960471, 2628717106, 2564626643, 2502596088, 2442537383, 2384367106, 2328006187, 2273379649, 2220416358, 2169048798, 2119212861, 2070847642, 2023895262, 1978300684, 1934011562, 1890978079, 1849152813, 1808490597, 1768948400, 1730485204, 1693061898, 1656641173, 1621187426, 1586666667, 1553046434, 1520295713, 1488384862, 1457285537, 1426970627, 1397414192, 1368591399, 1340478469, 1313052621, 1286292025, 1260175753, 1234683733, 1209796708, 1185496198, 1161764459, 1138584447, 1115939789, 1093814746, 1072194187, 1051063556, 1030408847, 1010216582, 990473781, 971167941, 952287016, 933819394, 915753879, 898079673, 880786356, 863863870, 847302505, 831092882, 815225939, 799692920, 784485356, 769595060, 755014110, 740734841, 726749832, 713051899, 699634081, 686489635, 673612028, 660994922, 648632176, 636517829, 624646099, 613011375, 601608209, 590431310, 579475540, 568735908, 558207560, 547885782, 537765987, 527843718, 518114635, 508574519, 499219261, 490044864, 481047436, 472223184, 463568416, 455079535, 446753036, 438585501, 430573600, 422714087, 415003793, 407439631, 400018587, 392737722, 385594165]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 689).prefactor = (919437985718427/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 689).cutoff/(generalMeanRows 689).c)).2 =
    (16709782586491/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 689).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 689).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 689).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 689

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 689).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 689).criticalRate j.val*(generalMeanRows 689).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 689).c*(generalMeanRows 689).criticalPoint j.val)).2-
      (generalMeanRows 689).J/2-(generalMeanRows 689).error (generalMeanGrid j.val)+
      (generalMeanRows 689).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 689).c)).2-
      (generalMeanRows 689).J/2-(generalMeanRows 689).error 4 := by
  have he : (generalMeanRows 689).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 689) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 689)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0689

/-! Kernel-checked entropy margins for general spectral rectangle 690. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0690
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5233402587, 5065691256, 4905353572, 4751967463, 4605140815, 4464508855, 4329731812, 4200492833, 4076496098, 3957465137, 3843141303, 3733282396, 3627661407, 3526065388, 3428294414, 3334160643, 3243487451, 3156108642, 3071867730, 2990617268, 2912218240, 2836539498, 2763457243, 2692854545, 2624620900, 2558651821, 2494848458, 2433117243, 2373369566, 2315521473, 2259493376, 2205209796, 2152599118, 2101593358, 2052127954, 2004141564, 1957575883, 1912375466, 1868487566, 1825861985, 1784450926, 1744208862, 1705092413, 1667060223, 1630072855, 1594092682, 1559083795, 1525011907, 1491844269, 1459549591, 1428097959, 1397460771, 1367610665, 1338521457, 1310168078, 1282526522, 1255573790, 1229287837, 1203647530, 1178632600, 1154223597, 1130401856, 1107149454, 1084449176, 1062284481, 1040639471, 1019498857, 998847936, 978672559, 958959107, 939694466, 920866006, 902461556, 884469387, 866878186, 849677044, 832855437, 816403205, 800310540, 784567969, 769166341, 754096813, 739350833, 724920136, 710796724, 696972860, 683441054, 670194054, 657224839, 644526606, 632092763, 619916919, 607992881, 596314640, 584876367, 573672406, 562697269, 551945626, 541412302, 531092270, 520980645, 511072681, 501363764, 491849409, 482525253, 473387052, 464430678, 455652114, 447047448, 438612873, 430344684, 422239268, 414293108, 406502779, 398864939, 391376335, 384033793, 376834220, 369774598, 362851984, 356063508]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 690).prefactor = (576612720338173/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 690).cutoff/(generalMeanRows 690).c)).2 =
    (82022187961441/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 690).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 690).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 690).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 690

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 690).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 690).criticalRate j.val*(generalMeanRows 690).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 690).c*(generalMeanRows 690).criticalPoint j.val)).2-
      (generalMeanRows 690).J/2-(generalMeanRows 690).error (generalMeanGrid j.val)+
      (generalMeanRows 690).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 690).c)).2-
      (generalMeanRows 690).J/2-(generalMeanRows 690).error 4 := by
  have he : (generalMeanRows 690).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 690) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 690)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0690

/-! Kernel-checked entropy margins for general spectral rectangle 691. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0691
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5165428963, 4997438274, 4836845416, 4683228349, 4536194919, 4395380247, 4260444400, 4131070308, 4006961892, 3887842377, 3773452776, 3663550514, 3557908180, 3456312399, 3358562797, 3264471062, 3173860087, 3086563181, 3002423348, 2921292624, 2843031471, 2767508214, 2694598520, 2624184929, 2556156404, 2490407925, 2426840112, 2365358874, 2305875077, 2248304248, 2192566289, 2138585218, 2086288918, 2035608917, 1986480169, 1938840858, 1892632212, 1847798330, 1804286018, 1762044637, 1721025963, 1681184049, 1642475105, 1604857375, 1568291032, 1532738069, 1498162205, 1464528795, 1431804738, 1399958400, 1368959539, 1338779229, 1309389795, 1280764750, 1252878731, 1225707446, 1199227619, 1173416938, 1148254011, 1123718317, 1099790166, 1076450656, 1053681639, 1031465681, 1009786031, 988626585, 967971861, 947806965, 928117566, 908889870, 890110595, 871766947, 853846600, 836337675, 819228715, 802508674, 786166894, 770193088, 754577328, 739310023, 724381913, 709784045, 695507769, 681544721, 667886811, 654526213, 641455354, 628666903, 616153762, 603909055, 591926124, 580198512, 568719965, 557484416, 546485983, 535718958, 525177804, 514857146, 504751767, 494856601, 485166725, 475677359, 466383858, 457281707, 448366516, 439634017, 431080058, 422700602, 414491720, 406449587, 398570483, 390850784, 383286961, 375875578, 368613288, 361496831, 354523027, 347688781, 340991073, 334426960, 327993571]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 691).prefactor = (4615776958851293/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 691).cutoff/(generalMeanRows 691).c)).2 =
    (99926572449567/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 691).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 691).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 691).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 691

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 691).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 691).criticalRate j.val*(generalMeanRows 691).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 691).c*(generalMeanRows 691).criticalPoint j.val)).2-
      (generalMeanRows 691).J/2-(generalMeanRows 691).error (generalMeanGrid j.val)+
      (generalMeanRows 691).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 691).c)).2-
      (generalMeanRows 691).J/2-(generalMeanRows 691).error 4 := by
  have he : (generalMeanRows 691).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 691) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 691)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0691

/-! Kernel-checked entropy margins for general spectral rectangle 692. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0692
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5183229130, 5014659542, 4853513279, 4699366845, 4551826734, 4410526812, 4275125973, 4145306056, 4020769960, 3901239957, 3786456167, 3676175179, 3570168800, 3468222918, 3370136469, 3275720492, 3184797270, 3097199538, 3012769757, 2931359455, 2852828613, 2777045100, 2703884159, 2633227921, 2564964968, 2498989918, 2435203050, 2373509946, 2313821166, 2256051947, 2200121915, 2145954824, 2093478310, 2042623664, 1993325618, 1945522141, 1899154259, 1854165879, 1810503622, 1768116677, 1726956651, 1686977442, 1648135106, 1610387745, 1573695393, 1538019914, 1503324901, 1469575589, 1436738764, 1404782683, 1373677000, 1343392688, 1313901978, 1285178290, 1257196176, 1229931258, 1203360180, 1177460556, 1152210917, 1127590672, 1103580064, 1080160126, 1057312646, 1035020132, 1013265773, 992033412, 971307511, 951073126, 931315877, 912021922, 893177933, 874771073, 856788972, 839219710, 822051793, 805274134, 788876040, 772847188, 757177616, 741857700, 726878147, 712229974, 697904502, 683893337, 670188362, 656781723, 643665821, 630833301, 618277039, 605990137, 593965912, 582197888, 570679785, 559405519, 548369184, 537565056, 526987577, 516631354, 506491152, 496561886, 486838619, 477316552, 467991026, 458857509, 449911596, 441149004, 432565568, 424157237, 415920066, 407850221, 399943965, 392197663, 384607775, 377170852, 369883537, 362742556, 355744721, 348886923, 342166135, 335579402, 329123844]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 692).prefactor = (4631683015102073/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 692).cutoff/(generalMeanRows 692).c)).2 =
    (99926572449567/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 692).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 692).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 692).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 692

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 692).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 692).criticalRate j.val*(generalMeanRows 692).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 692).c*(generalMeanRows 692).criticalPoint j.val)).2-
      (generalMeanRows 692).J/2-(generalMeanRows 692).error (generalMeanGrid j.val)+
      (generalMeanRows 692).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 692).c)).2-
      (generalMeanRows 692).J/2-(generalMeanRows 692).error 4 := by
  have he : (generalMeanRows 692).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 692) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 692)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0692

/-! Kernel-checked entropy margins for general spectral rectangle 693. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0693
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5052302938, 4883283509, 4721734416, 4567232123, 4419382951, 4277820473, 4142203186, 4012212430, 3887550521, 3767939072, 3653117476, 3542841531, 3436882206, 3335024502, 3237066429, 3142818070, 3052100720, 2964746103, 2880595656, 2799499864, 2721317654, 2645915838, 2573168595, 2502956992, 2435168550, 2369696829, 2306441055, 2245305767, 2186200492, 2129039443, 2073741236, 2020228630, 1968428282, 1918270516, 1869689115, 1822621120, 1777006643, 1732788696, 1689913028, 1648327969, 1607984293, 1568835079, 1530835588, 1493943145, 1458117029, 1423318366, 1389510035, 1356656572, 1324724087, 1293680180, 1263493866, 1234135502, 1205576717, 1177790351, 1150750392, 1124431920, 1098811050, 1073864887, 1049571472, 1025909737, 1002859467, 980401252, 958516456, 937187172, 916396196, 896126990, 876363648, 857090876, 838293952, 819958711, 802071513, 784619220, 767589178, 750969190, 734747498, 718912766, 703454058, 688360824, 673622880, 659230395, 645173875, 631444149, 618032357, 604929934, 592128600, 579620347, 567397432, 555452360, 543777877, 532366964, 521212820, 510308861, 499648709, 489226179, 479035281, 469070205, 459325317, 449795153, 440474411, 431357947, 422440768, 413718025, 405185012, 396837156, 388670016, 380679277, 372860744, 365210341, 357724105, 350398182, 343228823, 336212383, 329345314, 322624164, 316045573, 309606271, 303303074, 297132881, 291092673, 285179508, 279390522]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 693).prefactor = (72464783375401/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 693).cutoff/(generalMeanRows 693).c)).2 =
    (94772729616099/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 693).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 693).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 693).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 693

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 693).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 693).criticalRate j.val*(generalMeanRows 693).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 693).c*(generalMeanRows 693).criticalPoint j.val)).2-
      (generalMeanRows 693).J/2-(generalMeanRows 693).error (generalMeanGrid j.val)+
      (generalMeanRows 693).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 693).c)).2-
      (generalMeanRows 693).J/2-(generalMeanRows 693).error 4 := by
  have he : (generalMeanRows 693).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 693) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 693)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0693

/-! Kernel-checked entropy margins for general spectral rectangle 694. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0694
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5116913811, 4948099809, 4786732968, 4632389785, 4484676681, 4343227382, 4207700594, 4077777914, 3953161955, 3833574665, 3718755806, 3608461575, 3502463362, 3400546615, 3302509808, 3208163503, 3117329490, 3029839998, 2945536976, 2864271429, 2785902811, 2710298459, 2637333083, 2566888281, 2498852100, 2433118627, 2369587611, 2308164109, 2248758162, 2191284490, 2135662212, 2081814579, 2029668734, 1979155481, 1930209071, 1882767006, 1836769851, 1792161059, 1748886812, 1706895864, 1666139400, 1626570905, 1588146031, 1550822488, 1514559927, 1479319837, 1445065450, 1411761646, 1379374868, 1347873040, 1317225490, 1287402879, 1258377132, 1230121373, 1202609868, 1175817962, 1149722030, 1124299426, 1099528431, 1075388212, 1051858776, 1028920931, 1006556247, 984747020, 963476238, 942727549, 922485226, 902734145, 883459750, 864648034, 846285507, 828359178, 810856530, 793765500, 777074458, 760772188, 744847871, 729291067, 714091697, 699240031, 684726671, 670542536, 656678852, 643127136, 629879184, 616927064, 604263100, 591879862, 579770158, 567927027, 556343722, 545013710, 533930658, 523088428, 512481071, 502102813, 491948057, 482011371, 472287483, 462771275, 453457780, 444342170, 435419760, 426685994, 418136447, 409766816, 401572920, 393550691, 385696174, 378005520, 370474986, 363100928, 355879800, 348808149, 341882614, 335099921, 328456881, 321950388, 315577416, 309335014, 303220308]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 694).prefactor = (926941781704821/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 694).cutoff/(generalMeanRows 694).c)).2 =
    (389366581042601/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 694).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 694).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 694).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 694

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 694).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 694).criticalRate j.val*(generalMeanRows 694).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 694).c*(generalMeanRows 694).criticalPoint j.val)).2-
      (generalMeanRows 694).J/2-(generalMeanRows 694).error (generalMeanGrid j.val)+
      (generalMeanRows 694).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 694).c)).2-
      (generalMeanRows 694).J/2-(generalMeanRows 694).error 4 := by
  have he : (generalMeanRows 694).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 694) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 694)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0694

/-! Kernel-checked entropy margins for general spectral rectangle 695. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0695
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5050225782, 4881235149, 4719727063, 4565276360, 4417487885, 4275993876, 4140451620, 4010541367, 3885964449, 3766441591, 3651711389, 3541528926, 3435664528, 3333902622, 3236040709, 3141888415, 3051266633, 2964006732, 2879949835, 2798946156, 2720854383, 2645541124, 2572880381, 2502753075, 2435046600, 2369654415, 2306475664, 2245414820, 2186381363, 2129289472, 2074057744, 2020608927, 1968869680, 1918770339, 1870244705, 1823229846, 1777665908, 1733495940, 1690665735, 1649123671, 1608820572, 1569709572, 1531745990, 1494887209, 1459092569, 1424323257, 1390542216, 1357714045, 1325804918, 1294782500, 1264615869, 1235275446, 1206732924, 1178961205, 1151934340, 1125627468, 1100016768, 1075079400, 1050793465, 1027137952, 1004092701, 981638357, 959756336, 938428783, 917638545, 897369130, 877604684, 858329954, 839530266, 821191497, 803300048, 785842823, 768807205, 752181036, 735952595, 720110579, 704644087, 689542600, 674795966, 660394385, 646328390, 632588839, 619166897, 606054024, 593241967, 580722739, 568488620, 556532135, 544846052, 533423369, 522257307, 511341297, 500668978, 490234182, 480030932, 470053435, 460296069, 450753383, 441420089, 432291053, 423361292, 414625971, 406080390, 397719988, 389540331, 381537113, 373706147, 366043364, 358544807, 351206629, 344025089, 336996544, 330117453, 323384369, 316793936, 310342889, 304028046, 297846312, 291794670, 285870180, 280069982]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 695).prefactor = (581351666826837/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 695).cutoff/(generalMeanRows 695).c)).2 =
    (381903859841009/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 695).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 695).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 695).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 695

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 695).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 695).criticalRate j.val*(generalMeanRows 695).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 695).c*(generalMeanRows 695).criticalPoint j.val)).2-
      (generalMeanRows 695).J/2-(generalMeanRows 695).error (generalMeanGrid j.val)+
      (generalMeanRows 695).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 695).c)).2-
      (generalMeanRows 695).J/2-(generalMeanRows 695).error 4 := by
  have he : (generalMeanRows 695).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 695) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 695)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0695

/-! Kernel-checked entropy margins for general spectral rectangle 696. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0696
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5070005641, 4900393988, 4738278845, 4583235193, 4434867974, 4292809477, 4156717002, 4026270773, 3901172063, 3781141509, 3665917590, 3555255251, 3448924656, 3346710054, 3248408748, 3153830153, 3062794939, 2975134242, 2890688941, 2809308998, 2730852846, 2655186831, 2582184689, 2511727073, 2443701108, 2377999982, 2314522566, 2253173067, 2193860694, 2136499358, 2081007393, 2027307285, 1975325434, 1924991921, 1876240296, 1829007380, 1783233075, 1738860194, 1695834294, 1654103526, 1613618490, 1574332101, 1536199464, 1499177755, 1463226108, 1428305515, 1394378723, 1361410145, 1329365772, 1298213091, 1267921007, 1238459774, 1209800923, 1181917197, 1154782493, 1128371803, 1102661161, 1077627590, 1053249053, 1029504410, 1006373374, 983836469, 961874990, 940470971, 919607146, 899266918, 879434329, 860094026, 841231240, 822831755, 804881881, 787368438, 770278724, 753600501, 737321971, 721431756, 705918883, 690772763, 675983179, 661540264, 647434492, 633656659, 620197873, 607049541, 594203352, 581651272, 569385529, 557398603, 545683214, 534232318, 523039091, 512096927, 501399422, 490940373, 480713767, 470713774, 460934741, 451371185, 442017784, 432869377, 423920953, 415167647, 406604735, 398227629, 390031872, 382013134, 374167206, 366489997, 358977530, 351625938, 344431459, 337390434, 330499303, 323754603, 317152961, 310691097, 304365814, 298174001, 292112629, 286178745, 280369475]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 696).prefactor = (4653996279171663/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 696).cutoff/(generalMeanRows 696).c)).2 =
    (94772729616099/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 696).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 696).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 696).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 696

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 696).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 696).criticalRate j.val*(generalMeanRows 696).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 696).c*(generalMeanRows 696).criticalPoint j.val)).2-
      (generalMeanRows 696).J/2-(generalMeanRows 696).error (generalMeanGrid j.val)+
      (generalMeanRows 696).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 696).c)).2-
      (generalMeanRows 696).J/2-(generalMeanRows 696).error 4 := by
  have he : (generalMeanRows 696).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 696) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 696)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0696

/-! Kernel-checked entropy margins for general spectral rectangle 697. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0697
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5004693283, 4834933357, 4672705259, 4517582262, 4369167692, 4227092304, 4091011946, 3960605458, 3835572801, 3715633359, 3600524416, 3489999780, 3383828525, 3281793859, 3183692092, 3089331685, 2998532395, 2911124482, 2826947987, 2745852066, 2667694380, 2592340530, 2519663541, 2449543379, 2381866510, 2316525488, 2253418576, 2192449391, 2133526580, 2076563511, 2021477993, 1968192010, 1916631477, 1866726009, 1818408706, 1771615956, 1726287245, 1682364986, 1639794348, 1598523111, 1558501518, 1519682138, 1482019745, 1445471196, 1409995317, 1375552805, 1342106124, 1309619411, 1278058396, 1247390313, 1217583824, 1188608948, 1160436992, 1133040485, 1106393117, 1080469681, 1055246020, 1030698974, 1006806332, 983546785, 960899886, 938846004, 917366287, 896442629, 876057628, 856194558, 836837338, 817970498, 799579157, 781648992, 764166212, 747117538, 730490179, 714271807, 698450543, 683014929, 667953918, 653256852, 638913445, 624913769, 611248237, 597907591, 584882887, 572165482, 559747020, 547619425, 535774883, 524205838, 512904977, 501865224, 491079726, 480541850, 470245169, 460183459, 450350686, 440741003, 431348743, 422168407, 413194665, 404422345, 395846428, 387462043, 379264463, 371249096, 363411484, 355747297, 348252328, 340922490, 333753808, 326742422, 319884577, 313176621, 306615004, 300196271, 293917063, 287774109, 281764227, 275884319, 270131370, 264502444, 258994681]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 697).prefactor = (37362426887997/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 697).cutoff/(generalMeanRows 697).c)).2 =
    (46460434648317/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 697).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 697).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 697).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 697

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 697).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 697).criticalRate j.val*(generalMeanRows 697).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 697).c*(generalMeanRows 697).criticalPoint j.val)).2-
      (generalMeanRows 697).J/2-(generalMeanRows 697).error (generalMeanGrid j.val)+
      (generalMeanRows 697).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 697).c)).2-
      (generalMeanRows 697).J/2-(generalMeanRows 697).error 4 := by
  have he : (generalMeanRows 697).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 697) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 697)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0697

/-! Kernel-checked entropy margins for general spectral rectangle 698. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0698
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5139624639, 4970174667, 4808159314, 4653158583, 4504782035, 4362666215, 4226472343, 4095884256, 3970606559, 3850362962, 3734894779, 3623959571, 3517329916, 3414792294, 3316146067, 3221202554, 3129784181, 3041723709, 2956863518, 2875054958, 2796157746, 2720039413, 2646574795, 2575645557, 2507139766, 2440951477, 2376980367, 2315131384, 2255314429, 2197444050, 2141439170, 2087222823, 2034721913, 1983866993, 1934592046, 1886834294, 1840534014, 1795634363, 1752081220, 1709823031, 1668810673, 1628997315, 1590338300, 1552791021, 1516314819, 1480870873, 1446422106, 1412933094, 1380369979, 1348700389, 1317893358, 1287919262, 1258749742, 1230357649, 1202716974, 1175802802, 1149591247, 1124059411, 1099185330, 1074947930, 1051326987, 1028303080, 1005857561, 983972511, 962630711, 941815606, 921511277, 901702408, 882374263, 863512656, 845103928, 827134923, 809592963, 792465831, 775741751, 759409361, 743457706, 727876211, 712654672, 697783233, 683252378, 669052914, 655175955, 641612914, 628355486, 615395641, 602725609, 590337872, 578225153, 566380406, 554796808, 543467749, 532386824, 521547827, 510944739, 500571727, 490423131, 480493462, 470777392, 461269752, 451965521, 442859827, 433947935, 425225249, 416687300, 408329746, 400148368, 392139062, 384297838, 376620816, 369104221, 361744379, 354537717, 347480756, 340570108, 333802477, 327174650, 320683500, 314325981, 308099123, 302000034]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 698).prefactor = (18443755996309/4000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 698).cutoff/(generalMeanRows 698).c)).2 =
    (95237846029329/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 698).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 698).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 698).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 698

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 698).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 698).criticalRate j.val*(generalMeanRows 698).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 698).c*(generalMeanRows 698).criticalPoint j.val)).2-
      (generalMeanRows 698).J/2-(generalMeanRows 698).error (generalMeanGrid j.val)+
      (generalMeanRows 698).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 698).c)).2-
      (generalMeanRows 698).J/2-(generalMeanRows 698).error 4 := by
  have he : (generalMeanRows 698).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 698) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 698)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0698

/-! Kernel-checked entropy margins for general spectral rectangle 699. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0699
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5009022415, 4839224782, 4676933293, 4521724523, 4373204795, 4231007582, 4094791191, 3964236690, 3839046051, 3718940475, 3603658884, 3492956556, 3386603891, 3284385281, 3186098096, 3091551744, 3000566822, 2912974337, 2828614987, 2747338507, 2669003064, 2593474699, 2520626816, 2450339706, 2382500111, 2317000815, 2253740270, 2192622246, 2133555507, 2076453513, 2021234132, 1967819386, 1916135207, 1866111203, 1817680456, 1770779315, 1725347217, 1681326511, 1638662295, 1597302266, 1557196576, 1518297700, 1480560307, 1443941147, 1408398936, 1373894257, 1340389454, 1307848550, 1276237151, 1245522371, 1215672753, 1186658193, 1158449880, 1131020220, 1104342786, 1078392255, 1053144353, 1028575807, 1004664293, 981388394, 958727554, 936662037, 915172890, 894241904, 873851581, 853985100, 834626286, 815759582, 797370017, 779443184, 761965211, 744922741, 728302903, 712093298, 696281972, 680857403, 665808474, 651124463, 636795023, 622810168, 609160252, 595835964, 582828306, 570128585, 557728397, 545619619, 533794393, 522245121, 510964450, 499945263, 489180673, 478664009, 468388812, 458348825, 448537984, 438950413, 429580416, 420422470, 411471218, 402721466, 394168172, 385806443, 377631533, 369638830, 361823860, 354182275, 346709851, 339402487, 332256195, 325267100, 318431435, 311745538, 305205846, 298808895, 292551317, 286429831, 280441248, 274582462, 268850451, 263242272, 257755061]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 699).prefactor = (4643859518625529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 699).cutoff/(generalMeanRows 699).c)).2 =
    (45760152704733/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 699).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 699).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 699).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 699

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 699).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 699).criticalRate j.val*(generalMeanRows 699).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 699).c*(generalMeanRows 699).criticalPoint j.val)).2-
      (generalMeanRows 699).J/2-(generalMeanRows 699).error (generalMeanGrid j.val)+
      (generalMeanRows 699).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 699).c)).2-
      (generalMeanRows 699).J/2-(generalMeanRows 699).error 4 := by
  have he : (generalMeanRows 699).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 699) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 699)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0699

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock09 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 9 i) := by
  fin_cases i
  · exact EntropyRow0630.numerical
  · exact EntropyRow0631.numerical
  · exact EntropyRow0632.numerical
  · exact EntropyRow0633.numerical
  · exact EntropyRow0634.numerical
  · exact EntropyRow0635.numerical
  · exact EntropyRow0636.numerical
  · exact EntropyRow0637.numerical
  · exact EntropyRow0638.numerical
  · exact EntropyRow0639.numerical
  · exact EntropyRow0640.numerical
  · exact EntropyRow0641.numerical
  · exact EntropyRow0642.numerical
  · exact EntropyRow0643.numerical
  · exact EntropyRow0644.numerical
  · exact EntropyRow0645.numerical
  · exact EntropyRow0646.numerical
  · exact EntropyRow0647.numerical
  · exact EntropyRow0648.numerical
  · exact EntropyRow0649.numerical
  · exact EntropyRow0650.numerical
  · exact EntropyRow0651.numerical
  · exact EntropyRow0652.numerical
  · exact EntropyRow0653.numerical
  · exact EntropyRow0654.numerical
  · exact EntropyRow0655.numerical
  · exact EntropyRow0656.numerical
  · exact EntropyRow0657.numerical
  · exact EntropyRow0658.numerical
  · exact EntropyRow0659.numerical
  · exact EntropyRow0660.numerical
  · exact EntropyRow0661.numerical
  · exact EntropyRow0662.numerical
  · exact EntropyRow0663.numerical
  · exact EntropyRow0664.numerical
  · exact EntropyRow0665.numerical
  · exact EntropyRow0666.numerical
  · exact EntropyRow0667.numerical
  · exact EntropyRow0668.numerical
  · exact EntropyRow0669.numerical
  · exact EntropyRow0670.numerical
  · exact EntropyRow0671.numerical
  · exact EntropyRow0672.numerical
  · exact EntropyRow0673.numerical
  · exact EntropyRow0674.numerical
  · exact EntropyRow0675.numerical
  · exact EntropyRow0676.numerical
  · exact EntropyRow0677.numerical
  · exact EntropyRow0678.numerical
  · exact EntropyRow0679.numerical
  · exact EntropyRow0680.numerical
  · exact EntropyRow0681.numerical
  · exact EntropyRow0682.numerical
  · exact EntropyRow0683.numerical
  · exact EntropyRow0684.numerical
  · exact EntropyRow0685.numerical
  · exact EntropyRow0686.numerical
  · exact EntropyRow0687.numerical
  · exact EntropyRow0688.numerical
  · exact EntropyRow0689.numerical
  · exact EntropyRow0690.numerical
  · exact EntropyRow0691.numerical
  · exact EntropyRow0692.numerical
  · exact EntropyRow0693.numerical
  · exact EntropyRow0694.numerical
  · exact EntropyRow0695.numerical
  · exact EntropyRow0696.numerical
  · exact EntropyRow0697.numerical
  · exact EntropyRow0698.numerical
  · exact EntropyRow0699.numerical
end SingularValueBounds.KL.Certificates
