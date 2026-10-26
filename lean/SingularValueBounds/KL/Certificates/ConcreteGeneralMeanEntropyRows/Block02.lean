import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 140. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0140
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4976274638, 4798590282, 4629235032, 4467716315, 4313576995, 4166392280, 4025766956, 3891332914, 3762746923, 3639688629, 3521858737, 3408977382, 3300782634, 3197029153, 3097486953, 3001940282, 2910186597, 2822035617, 2737308470, 2655836896, 2577462520, 2502036182, 2429417321, 2359473402, 2292079391, 2227117265, 2164475566, 2104048977, 2045737934, 1989448271, 1935090880, 1882581401, 1831839932, 1782790761, 1735362112, 1689485908, 1645097558, 1602135748, 1560542251, 1520261748, 1481241660, 1443431993, 1406785191, 1371255999, 1336801333, 1303380158, 1270953380, 1239483734, 1208935688, 1179275347, 1150470365, 1122489864, 1095304355, 1068885662, 1043206857, 1018242195, 993967050, 970357856, 947392060, 925048063, 903305176, 882143572, 861544244, 841488967, 821960254, 802941325, 784416071, 766369018, 748785304, 731650645, 714951306, 698674079, 682806260, 667335619, 652250383, 637539215, 623191194, 609195795, 595542871, 582222639, 569225661, 556542832, 544165362, 532084765, 520292846, 508781686, 497543634, 486571293, 475857512, 465395373, 455178185, 445199470, 435452960, 425932585, 416632465, 407546906, 398670388, 389997562, 381523243, 373242401, 365150160, 357241786, 349512688, 341958409, 334574621, 327357124, 320301836, 313404793, 306662145, 300070147, 293625162, 287323652, 281162179, 275137398, 269246056, 263484986, 257851110, 252341431, 246953031, 241683070, 236528782]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 140).prefactor = (2547702846077973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 140).cutoff/(generalMeanRows 140).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 140).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 140).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 140).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 140

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 140).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 140).criticalRate j.val*(generalMeanRows 140).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 140).c*(generalMeanRows 140).criticalPoint j.val)).2-
      (generalMeanRows 140).J/2-(generalMeanRows 140).error (generalMeanGrid j.val)+
      (generalMeanRows 140).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 140).c)).2-
      (generalMeanRows 140).J/2-(generalMeanRows 140).error 4 := by
  have he : (generalMeanRows 140).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 140) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 140)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0140

/-! Kernel-checked entropy margins for general spectral rectangle 141. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0141
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5158507339, 4982433128, 4814583217, 4654464904, 4501621277, 4355628092, 4216090973, 4082642900, 3954941959, 3832669308, 3715527346, 3603238044, 3495541447, 3392194297, 3292968784, 3197651414, 3106041962, 3017952519, 2933206622, 2851638447, 2773092077, 2697420818, 2624486575, 2554159276, 2486316336, 2420842166, 2357627717, 2296570055, 2237571970, 2180541611, 2125392153, 2072041475, 2020411873, 1970429791, 1922025558, 1875133161, 1829690022, 1785636791, 1742917157, 1701477664, 1661267551, 1622238588, 1584344935, 1547543000, 1511791315, 1477050413, 1443282717, 1410452432, 1378525447, 1347469242, 1317252802, 1287846532, 1259222180, 1231352770, 1204212526, 1177776812, 1152022074, 1126925779, 1102466362, 1078623179, 1055376458, 1032707252, 1010597399, 989029486, 967986802, 947453315, 927413627, 907852950, 888757076, 870112344, 851905618, 834124262, 816756113, 799789461, 783213030, 767015952, 751187753, 735718335, 720597955, 705817214, 691367038, 677238665, 663423632, 649913760, 636701143, 623778138, 611137351, 598771627, 586674041, 574837888, 563256675, 551924111, 540834099, 529980729, 519358269, 508961162, 498784014, 488821591, 479068812, 469520743, 460172593, 451019705, 442057556, 433281748, 424688007, 416272175, 408030209, 399958173, 392052241, 384308687, 376723881, 369294294, 362016484, 354887102, 347902883, 341060645, 334357289, 327789793, 321355209, 315050665, 308873358]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 141).prefactor = (127090417059439/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 141).cutoff/(generalMeanRows 141).c)).2 =
    (87367277932881/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 141).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 141).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 141).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 141

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 141).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 141).criticalRate j.val*(generalMeanRows 141).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 141).c*(generalMeanRows 141).criticalPoint j.val)).2-
      (generalMeanRows 141).J/2-(generalMeanRows 141).error (generalMeanGrid j.val)+
      (generalMeanRows 141).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 141).c)).2-
      (generalMeanRows 141).J/2-(generalMeanRows 141).error 4 := by
  have he : (generalMeanRows 141).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 141) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 141)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0141

/-! Kernel-checked entropy margins for general spectral rectangle 142. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0142
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5191653435, 5014447856, 4845519422, 4684372265, 4530546538, 4383615272, 4243181554, 4108876007, 3980354521, 3857296205, 3739401544, 3626390726, 3518002122, 3413990912, 3314127824, 3218197990, 3125999899, 3037344436, 2952054002, 2869961710, 2790910638, 2714753152, 2641350268, 2570571079, 2502292213, 2436397338, 2372776703, 2311326714, 2251949535, 2194552727, 2139048904, 2085355420, 2033394072, 1983090828, 1934375573, 1887181868, 1841446733, 1797110438, 1754116307, 1712410544, 1671942060, 1632662316, 1594525176, 1557486770, 1521505362, 1486541232, 1452556560, 1419515323, 1387383191, 1356127434, 1325716837, 1296121616, 1267313339, 1239264853, 1211950218, 1185344642, 1159424416, 1134166864, 1109550283, 1085553895, 1062157801, 1039342934, 1017091014, 995384515, 974206622, 953541196, 933372742, 913686378, 894467803, 875703269, 857379555, 839483945, 822004196, 804928525, 788245582, 771944429, 756014526, 740445708, 725228172, 710352457, 695809431, 681590276, 667686474, 654089794, 640792280, 627786238, 615064227, 602619046, 590443727, 578531521, 566875893, 555470511, 544309240, 533386131, 522695417, 512231503, 501988962, 491962525, 482147079, 472537659, 463129441, 453917741, 444898006, 436065809, 427416849, 418946941, 410652015, 402528113, 394571381, 386778070, 379144528, 371667202, 364342629, 357167437, 350138340, 343252138, 336505709, 329896013, 323420084, 317075030, 310858031]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 142).prefactor = (639535195927343/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 142).cutoff/(generalMeanRows 142).c)).2 =
    (87367277932881/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 142).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 142).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 142).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 142

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 142).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 142).criticalRate j.val*(generalMeanRows 142).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 142).c*(generalMeanRows 142).criticalPoint j.val)).2-
      (generalMeanRows 142).J/2-(generalMeanRows 142).error (generalMeanGrid j.val)+
      (generalMeanRows 142).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 142).c)).2-
      (generalMeanRows 142).J/2-(generalMeanRows 142).error 4 := by
  have he : (generalMeanRows 142).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 142) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 142)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0142

/-! Kernel-checked entropy margins for general spectral rectangle 143. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0143
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4785520765, 4607335862, 4437607720, 4275836841, 4121559570, 3974344971, 3833792029, 3699527156, 3571201933, 3448491090, 3331090674, 3218716395, 3111102122, 3007998516, 2909171789, 2814402569, 2723484857, 2636225085, 2552441239, 2471962063, 2394626319, 2320282113, 2248786271, 2180003758, 2113807152, 2050076144, 1988697088, 1929562572, 1872571031, 1817626378, 1764637669, 1713518785, 1664188140, 1616568407, 1570586264, 1526172156, 1483260075, 1441787348, 1401694449, 1362924814, 1325424673, 1289142892, 1254030823, 1220042165, 1187132834, 1155260843, 1124386180, 1094470708, 1065478059, 1037373539, 1010124042, 983697960, 958065110, 933196655, 909065034, 885643900, 862908053, 840833383, 819396816, 798576260, 778350555, 758699431, 739603457, 721044007, 703003216, 685463944, 668409741, 651824816, 635694003, 620002733, 604737004, 589883358, 575428853, 561361039, 547667938, 534338022, 521360189, 508723749, 496418403, 484434226, 472761652, 461391455, 450314740, 439522921, 429007716, 418761128, 408775436, 399043184, 389557168, 380310427, 371296230, 362508074, 353939667, 345584924, 337437957, 329493067, 321744740, 314187636, 306816583, 299626573, 292612751, 285770415, 279095008, 272582110, 266227436, 260026831, 253976265, 248071827, 242309722, 236686266, 231197885, 225841108, 220612564, 215508980, 210527175, 205664060, 200916633, 196281978, 191757258, 187339718, 183026677]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 143).prefactor = (5163157018574371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 143).cutoff/(generalMeanRows 143).c)).2 =
    (94157389617073/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 143).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 143).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 143).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 143

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 143).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 143).criticalRate j.val*(generalMeanRows 143).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 143).c*(generalMeanRows 143).criticalPoint j.val)).2-
      (generalMeanRows 143).J/2-(generalMeanRows 143).error (generalMeanGrid j.val)+
      (generalMeanRows 143).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 143).c)).2-
      (generalMeanRows 143).J/2-(generalMeanRows 143).error 4 := by
  have he : (generalMeanRows 143).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 143) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 143)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0143

/-! Kernel-checked entropy margins for general spectral rectangle 144. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0144
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5291937287, 5121006341, 4957948209, 4802289177, 4653590113, 4511443444, 4375470449, 4245318827, 4120660519, 4001189740, 3886621204, 3776688514, 3671142703, 3569750909, 3472295165, 3378571296, 3288387913, 3201565489, 3117935515, 3037339721, 2959629365, 2884664577, 2812313748, 2742452979, 2674965559, 2609741495, 2546677065, 2485674410, 2426641159, 2369490077, 2314138734, 2260509208, 2208527800, 2158124771, 2109234102, 2061793260, 2015742992, 1971027124, 1927592379, 1885388201, 1844366595, 1804481979, 1765691040, 1727952607, 1691227520, 1655478522, 1620670146, 1586768617, 1553741755, 1521558886, 1490190759, 1459609467, 1429788372, 1400702041, 1372326173, 1344637545, 1317613950, 1291234146, 1265477801, 1240325451, 1215758449, 1191758927, 1168309753, 1145394497, 1122997391, 1101103298, 1079697680, 1058766570, 1038296541, 1018274681, 998688568, 979526245, 960776201, 942427346, 924468993, 906890840, 889682951, 872835737, 856339945, 840186640, 824367189, 808873251, 793696762, 778829924, 764265192, 749995264, 736013071, 722311767, 708884720, 695725500, 682827875, 670185803, 657793419, 645645033, 633735123, 622058325, 610609429, 599383373, 588375239, 577580244, 566993737, 556611194, 546428215, 536440516, 526643927, 517034388, 507607945, 498360746, 489289038, 480389162, 471657552, 463090732, 454685311, 446437981, 438345515, 430404765, 422612657, 414966192, 407462439, 400098540, 392871699]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 144).prefactor = (2471111901445491/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 144).cutoff/(generalMeanRows 144).c)).2 =
    (2325398009889/5000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 144).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 144).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 144).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 144

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 144).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 144).criticalRate j.val*(generalMeanRows 144).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 144).c*(generalMeanRows 144).criticalPoint j.val)).2-
      (generalMeanRows 144).J/2-(generalMeanRows 144).error (generalMeanGrid j.val)+
      (generalMeanRows 144).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 144).c)).2-
      (generalMeanRows 144).J/2-(generalMeanRows 144).error 4 := by
  have he : (generalMeanRows 144).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 144) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 144)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0144

/-! Kernel-checked entropy margins for general spectral rectangle 145. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0145
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7666569635, 7424066346, 7191741514, 6969048332, 6755477747, 6550555073, 6353836989, 6164908879, 5983382445, 5808893580, 5641100456, 5479681799, 5324335341, 5174776405, 5030736639, 4891962845, 4758215930, 4629269938, 4504911165, 4384937350, 4269156931, 4157388364, 4049459485, 3945206936, 3844475619, 3747118207, 3652994674, 3561971871, 3473923125, 3388727872, 3306271307, 3226444068, 3149141928, 3074265522, 3001720076, 2931415169, 2863264496, 2797185656, 2733099946, 2670932173, 2610610473, 2552066140, 2495233474, 2440049625, 2386454453, 2334390398, 2283802350, 2234637536, 2186845402, 2140377511, 2095187440, 2051230688, 2008464583, 1966848201, 1926342281, 1886909151, 1848512654, 1811118081, 1774692106, 1739202719, 1704619174, 1670911928, 1638052590, 1606013870, 1574769529, 1544294338, 1514564028, 1485555253, 1457245548, 1429613295, 1402637680, 1376298667, 1350576961, 1325453975, 1300911805, 1276933198, 1253501529, 1230600770, 1208215468, 1186330722, 1164932161, 1144005919, 1123538621, 1103517355, 1083929660, 1064763505, 1046007274, 1027649747, 1009680085, 992087817, 974862824, 957995325, 941475864, 925295300, 909444790, 893915782, 878700001, 863789441, 849176353, 834853235, 820812824, 807048087, 793552212, 780318599, 767340853, 754612777, 742128364, 729881789, 717867407, 706079738, 694513471, 683163449, 672024672, 661092282, 650361567, 639827950, 629486986, 619334359, 609365874, 599577455, 589965142]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 145).prefactor = (5481888854182377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 145).cutoff/(generalMeanRows 145).c)).2 =
    (331982331348377/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 145).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 145).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 145).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 145

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 145).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 145).criticalRate j.val*(generalMeanRows 145).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 145).c*(generalMeanRows 145).criticalPoint j.val)).2-
      (generalMeanRows 145).J/2-(generalMeanRows 145).error (generalMeanGrid j.val)+
      (generalMeanRows 145).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 145).c)).2-
      (generalMeanRows 145).J/2-(generalMeanRows 145).error 4 := by
  have he : (generalMeanRows 145).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 145) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 145)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0145

/-! Kernel-checked entropy margins for general spectral rectangle 146. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0146
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6431762543, 6244529767, 6065383708, 5893870999, 5729569891, 5572087484, 5421057246, 5276136814, 5137006018, 5003365105, 4874933143, 4751446579, 4632657933, 4518334611, 4408257829, 4302221632, 4200031995, 4101506000, 4006471089, 3914764367, 3826231970, 3740728477, 3658116372, 3578265542, 3501052816, 3426361539, 3354081169, 3284106917, 3216339396, 3150684307, 3087052139, 3025357895, 2965520829, 2907464208, 2851115084, 2796404085, 2743265212, 2691635659, 2641455636, 2592668207, 2545219134, 2499056736, 2454131754, 2410397217, 2367808333, 2326322364, 2285898530, 2246497902, 2208083309, 2170619251, 2134071810, 2098408575, 2063598566, 2029612159, 1996421025, 1963998060, 1932317330, 1901354011, 1871084338, 1841485550, 1812535845, 1784214333, 1756500993, 1729376629, 1702822836, 1676821961, 1651357064, 1626411890, 1601970835, 1578018917, 1554541744, 1531525491, 1508956872, 1486823118, 1465111950, 1443811558, 1422910583, 1402398092, 1382263563, 1362496866, 1343088243, 1324028297, 1305307968, 1286918529, 1268851562, 1251098949, 1233652860, 1216505739, 1199650291, 1183079474, 1166786488, 1150764761, 1135007944, 1119509899, 1104264692, 1089266583, 1074510020, 1059989629, 1045700207, 1031636718, 1017794282, 1004168174, 990753812, 977546756, 964542698, 951737463, 939126997, 926707368, 914474756, 902425455, 890555862, 878862477, 867341901, 855990825, 844806036, 833784405, 822922891, 812218530, 801668441, 791269816, 781019921]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 146).prefactor = (2296859273620447/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 146).cutoff/(generalMeanRows 146).c)).2 =
    (42927014928109/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 146).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 146).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 146).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 146

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 146).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 146).criticalRate j.val*(generalMeanRows 146).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 146).c*(generalMeanRows 146).criticalPoint j.val)).2-
      (generalMeanRows 146).J/2-(generalMeanRows 146).error (generalMeanGrid j.val)+
      (generalMeanRows 146).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 146).c)).2-
      (generalMeanRows 146).J/2-(generalMeanRows 146).error 4 := by
  have he : (generalMeanRows 146).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 146) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 146)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0146

/-! Kernel-checked entropy margins for general spectral rectangle 147. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0147
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6560513340, 6365963151, 6179821105, 6001616623, 5830911934, 5667299194, 5510397923, 5359852713, 5215331183, 5076522132, 4943133887, 4814892804, 4691541912, 4572839685, 4458558921, 4348485729, 4242418590, 4140167512, 4041553245, 3946406566, 3854567620, 3765885311, 3680216740, 3597426690, 3517387147, 3439976852, 3365080894, 3292590325, 3222401802, 3154417264, 3088543614, 3024692439, 2962779739, 2902725675, 2844454338, 2787893527, 2732974543, 2679632001, 2627803645, 2577430181, 2528455117, 2480824614, 2434487346, 2389394367, 2345498985, 2302756651, 2261124841, 2220562957, 2181032225, 2142495608, 2104917712, 2068264710, 2032504257, 1997605423, 1963538619, 1930275533, 1897789066, 1866053276, 1835043317, 1804735394, 1775106703, 1746135393, 1717800513, 1690081975, 1662960511, 1636417636, 1610435608, 1584997398, 1560086654, 1535687672, 1511785364, 1488365231, 1465413338, 1442916285, 1420861186, 1399235643, 1378027729, 1357225961, 1336819285, 1316797054, 1297149013, 1277865280, 1258936329, 1240352978, 1222106371, 1204187964, 1186589514, 1169303065, 1152320934, 1135635703, 1119240205, 1103127515, 1087290940, 1071724009, 1056420462, 1041374245, 1026579499, 1012030554, 997721920, 983648278, 969804478, 956185527, 942786588, 929602969, 916630120, 903863627, 891299208, 878932706, 866760082, 854777419, 842980906, 831366845, 819931638, 808671788, 797583895, 786664650, 775910834, 765319316, 754887046, 744611052, 734488445]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 147).prefactor = (954604190680271/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 147).cutoff/(generalMeanRows 147).c)).2 =
    (419270065946507/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 147).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 147).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 147).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 147

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 147).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 147).criticalRate j.val*(generalMeanRows 147).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 147).c*(generalMeanRows 147).criticalPoint j.val)).2-
      (generalMeanRows 147).J/2-(generalMeanRows 147).error (generalMeanGrid j.val)+
      (generalMeanRows 147).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 147).c)).2-
      (generalMeanRows 147).J/2-(generalMeanRows 147).error 4 := by
  have he : (generalMeanRows 147).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 147) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 147)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0147

/-! Kernel-checked entropy margins for general spectral rectangle 148. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0148
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6692777244, 6490698033, 6297361346, 6112278680, 5934995578, 5765088636, 5602162845, 5445849208, 5295802621, 5151699956, 5013238347, 4880133632, 4752118947, 4628943455, 4510371178, 4396179948, 4286160433, 4180115261, 4077858203, 3979213434, 3884014847, 3792105423, 3703336647, 3617567977, 3534666339, 3454505672, 3376966499, 3301935531, 3229305298, 3158973803, 3090844208, 3024824533, 2960827374, 2898769652, 2838572360, 2780160343, 2723462083, 2668409497, 2614937754, 2562985095, 2512492672, 2463404392, 2415666768, 2369228788, 2324041781, 2280059297, 2237236994, 2195532528, 2154905453, 2115317124, 2076730605, 2039110587, 2002423305, 1966636459, 1931719149, 1897641797, 1864376090, 1831894916, 1800172307, 1769183381, 1738904294, 1709312190, 1680385149, 1652102153, 1624443033, 1597388436, 1570919787, 1545019249, 1519669691, 1494854659, 1470558339, 1446765531, 1423461625, 1400632566, 1378264837, 1356345429, 1334861824, 1313801969, 1293154257, 1272907508, 1253050949, 1233574197, 1214467243, 1195720436, 1177324463, 1159270344, 1141549406, 1124153281, 1107073887, 1090303417, 1073834327, 1057659327, 1041771371, 1026163643, 1010829552, 995762720, 980956974, 966406340, 952105030, 938047441, 924228142, 910641872, 897283528, 884148163, 871230981, 858527326, 846032680, 833742658, 821653003, 809759579, 798058368, 786545467, 775217081, 764069520, 753099197, 742302621, 731676397, 721217219, 710921870, 700787217, 690810210]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 148).prefactor = (247966095303027/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 148).cutoff/(generalMeanRows 148).c)).2 =
    (409368994963797/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 148).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 148).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 148).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 148

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 148).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 148).criticalRate j.val*(generalMeanRows 148).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 148).c*(generalMeanRows 148).criticalPoint j.val)).2-
      (generalMeanRows 148).J/2-(generalMeanRows 148).error (generalMeanGrid j.val)+
      (generalMeanRows 148).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 148).c)).2-
      (generalMeanRows 148).J/2-(generalMeanRows 148).error 4 := by
  have he : (generalMeanRows 148).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 148) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 148)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0148

/-! Kernel-checked entropy margins for general spectral rectangle 149. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0149
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6248086250, 6039934606, 5840904062, 5650488707, 5468217782, 5293652580, 5126383704, 4966028611, 4812229414, 4664650914, 4522978819, 4386918144, 4256191758, 4130539070, 4009714827, 3893488029, 3781640927, 3673968118, 3570275703, 3470380525, 3374109460, 3281298772, 3191793508, 3105446949, 3022120097, 2941681196, 2864005299, 2788973854, 2716474328, 2646399850, 2578648886, 2513124927, 2449736207, 2388395434, 2329019538, 2271529441, 2215849833, 2161908968, 2109638476, 2058973175, 2009850906, 1962212370, 1916000984, 1871162732, 1827646037, 1785401637, 1744382463, 1704543529, 1665841830, 1628236241, 1591687421, 1556157729, 1521611139, 1488013161, 1455330765, 1423532314, 1392587494, 1362467251, 1333143733, 1304590233, 1276781134, 1249691857, 1223298816, 1197579370, 1172511780, 1148075167, 1124249474, 1101015427, 1078354502, 1056248890, 1034681465, 1013635754, 993095907, 973046672, 953473366, 934361853, 915698518, 897470245, 879664397, 862268794, 845271693, 828661773, 812428111, 796560173, 781047792, 765881154, 751050786, 736547538, 722362573, 708487353, 694913628, 681633420, 668639021, 655922971, 643478059, 631297305, 619373956, 607701473, 596273527, 585083989, 574126921, 563396570, 552887361, 542593891, 532510922, 522633372, 512956315, 503474970, 494184699, 485080999, 476159500, 467415957, 458846251, 450446377, 442212446, 434140677, 426227397, 418469035, 410862117, 403403266, 396089196]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 149).prefactor = (5152894573070153/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 149).cutoff/(generalMeanRows 149).c)).2 =
    (351936945877921/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 149).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 149).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 149).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 149

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 149).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 149).criticalRate j.val*(generalMeanRows 149).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 149).c*(generalMeanRows 149).criticalPoint j.val)).2-
      (generalMeanRows 149).J/2-(generalMeanRows 149).error (generalMeanGrid j.val)+
      (generalMeanRows 149).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 149).c)).2-
      (generalMeanRows 149).J/2-(generalMeanRows 149).error 4 := by
  have he : (generalMeanRows 149).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 149) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 149)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0149

/-! Kernel-checked entropy margins for general spectral rectangle 150. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0150
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6170875258, 5981473352, 5800390216, 5627153277, 5461323156, 5302490763, 5150274714, 5004319013, 4864290987, 4729879417, 4600792862, 4476758136, 4357518939, 4242834600, 4132478945, 4026239260, 3923915339, 3825318621, 3730271394, 3638606062, 3550164475, 3464797306, 3382363486, 3302729669, 3225769748, 3151364399, 3079400666, 3009771567, 2942375733, 2877117073, 2813904459, 2752651435, 2693275942, 2635700065, 2579849796, 2525654808, 2473048254, 2421966563, 2372349265, 2324138817, 2277280440, 2231721974, 2187413730, 2144308362, 2102360739, 2061527828, 2021768584, 1983043845, 1945316234, 1908550065, 1872711260, 1837767261, 1803686955, 1770440603, 1737999766, 1706337243, 1675427009, 1645244153, 1615764830, 1586966201, 1558826389, 1531324427, 1504440221, 1478154502, 1452448788, 1427305348, 1402707163, 1378637897, 1355081861, 1332023983, 1309449782, 1287345338, 1265697265, 1244492691, 1223719232, 1203364967, 1183418422, 1163868546, 1144704696, 1125916613, 1107494411, 1089428557, 1071709858, 1054329442, 1037278748, 1020549512, 1004133752, 988023759, 972212083, 956691523, 941455116, 926496129, 911808046, 897384563, 883219576, 869307175, 855641634, 842217407, 829029117, 816071552, 803339656, 790828526, 778533404, 766449671, 754572844, 742898566, 731422608, 720140859, 709049323, 698144116, 687421459, 676877678, 666509196, 656312534, 646284303, 636421204, 626720024, 617177631, 607790976, 598557084, 589473057]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 150).prefactor = (1209763506126581/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 150).cutoff/(generalMeanRows 150).c)).2 =
    (420929817364873/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 150).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 150).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 150).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 150

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 150).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 150).criticalRate j.val*(generalMeanRows 150).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 150).c*(generalMeanRows 150).criticalPoint j.val)).2-
      (generalMeanRows 150).J/2-(generalMeanRows 150).error (generalMeanGrid j.val)+
      (generalMeanRows 150).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 150).c)).2-
      (generalMeanRows 150).J/2-(generalMeanRows 150).error 4 := by
  have he : (generalMeanRows 150).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 150) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 150)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0150

/-! Kernel-checked entropy margins for general spectral rectangle 151. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0151
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5638460902, 5444969620, 5260133239, 5083464053, 4914508454, 4752843951, 4598076512, 4449838191, 4307784997, 4171594982, 4040966515, 3915616726, 3795280090, 3679707148, 3568663337, 3461927930, 3359293058, 3260562826, 3165552495, 3074087731, 2986003918, 2901145521, 2819365503, 2740524778, 2664491718, 2591141682, 2520356591, 2452024526, 2386039357, 2322300399, 2260712091, 2201183695, 2143629017, 2087966147, 2034117215, 1982008161, 1931568525, 1882731245, 1835432470, 1789611386, 1745210050, 1702173235, 1660448285, 1619984979, 1580735403, 1542653828, 1505696597, 1469822017, 1434990259, 1401163263, 1368304646, 1336379621, 1305354914, 1275198690, 1245880481, 1217371118, 1189642671, 1162668383, 1136422617, 1110880801, 1086019377, 1061815753, 1038248256, 1015296091, 992939297, 971158709, 949935924, 929253260, 909093730, 889441003, 870279379, 851593761, 833369624, 815592991, 798250412, 781328935, 764816089, 748699860, 732968672, 717611368, 702617194, 687975778, 673677114, 659711553, 646069778, 632742798, 619721930, 606998791, 594565278, 582413564, 570536084, 558925524, 547574808, 536477097, 525625771, 515014423, 504636854, 494487059, 484559225, 474847720, 465347088, 456052040, 446957452, 438058354, 429349927, 420827496, 412486526, 404322617, 396331496, 388509017, 380851155, 373353997, 366013746, 358826711, 351789304, 344898040, 338149530, 331540479, 325067680, 318728018, 312518458]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 151).prefactor = (5005829017144073/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 151).cutoff/(generalMeanRows 151).c)).2 =
    (357845841938297/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 151).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 151).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 151).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 151

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 151).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 151).criticalRate j.val*(generalMeanRows 151).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 151).c*(generalMeanRows 151).criticalPoint j.val)).2-
      (generalMeanRows 151).J/2-(generalMeanRows 151).error (generalMeanGrid j.val)+
      (generalMeanRows 151).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 151).c)).2-
      (generalMeanRows 151).J/2-(generalMeanRows 151).error 4 := by
  have he : (generalMeanRows 151).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 151) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 151)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0151

/-! Kernel-checked entropy margins for general spectral rectangle 152. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0152
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5628124114, 5453128331, 5285930931, 5126080525, 4973157784, 4826772643, 4686561806, 4552186510, 4423330523, 4299698336, 4181013538, 4067017340, 3957467242, 3852135816, 3750809603, 3653288103, 3559382855, 3468916591, 3381722465, 3297643335, 3216531118, 3138246179, 3062656780, 2989638565, 2919074083, 2850852351, 2784868445, 2721023123, 2659222470, 2599377577, 2541404232, 2485222641, 2430757163, 2377936060, 2326691277, 2276958216, 2228675545, 2181785004, 2136231235, 2091961612, 2048926092, 2007077068, 1966369234, 1926759458, 1888206663, 1850671715, 1814117317, 1778507911, 1743809584, 1709989980, 1677018218, 1644864816, 1613501614, 1582901709, 1553039387, 1523890064, 1495430225, 1467637374, 1440489977, 1413967419, 1388049953, 1362718660, 1337955407, 1313742808, 1290064185, 1266903540, 1244245513, 1222075360, 1200378917, 1179142576, 1158353255, 1137998377, 1118065846, 1098544020, 1079421695, 1060688083, 1042332791, 1024345808, 1006717481, 989438503, 972499899, 955893007, 939609466, 923641204, 907980423, 892619589, 877551420, 862768876, 848265145, 834033641, 820067984, 806362003, 792909716, 779705332, 766743237, 754017988, 741524310, 729257082, 717211339, 705382259, 693765163, 682355504, 671148867, 660140961, 649327615, 638704774, 628268494, 618014938, 607940373, 598041164, 588313775, 578754759, 569360760, 560128509, 551054819, 542136583, 533370773, 524754434, 516284686, 507958717, 499773783]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 152).prefactor = (1167758891265089/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 152).cutoff/(generalMeanRows 152).c)).2 =
    (218165094345907/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 152).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 152).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 152).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 152

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 152).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 152).criticalRate j.val*(generalMeanRows 152).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 152).c*(generalMeanRows 152).criticalPoint j.val)).2-
      (generalMeanRows 152).J/2-(generalMeanRows 152).error (generalMeanGrid j.val)+
      (generalMeanRows 152).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 152).c)).2-
      (generalMeanRows 152).J/2-(generalMeanRows 152).error 4 := by
  have he : (generalMeanRows 152).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 152) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 152)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0152

/-! Kernel-checked entropy margins for general spectral rectangle 153. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0153
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5304960183, 5126193145, 4955502900, 4792424906, 4636527493, 4487408990, 4344695170, 4208036959, 4077108383, 3951604717, 3831240817, 3715749614, 3604880739, 3498399287, 3396084680, 3297729635, 3203139223, 3112130001, 3024529220, 2940174100, 2858911156, 2780595585, 2705090693, 2632267371, 2562003610, 2494184048, 2428699556, 2365446848, 2304328123, 2245250730, 2188126860, 2132873250, 2079410920, 2027664916, 1977564079, 1929040821, 1882030925, 1836473348, 1792310044, 1749485796, 1707948056, 1667646799, 1628534384, 1590565423, 1553696659, 1517886851, 1483096667, 1449288579, 1416426774, 1384477055, 1353406764, 1323184699, 1293781038, 1265167270, 1237316126, 1210201518, 1183798480, 1158083106, 1133032506, 1108624748, 1084838814, 1061654557, 1039052654, 1017014569, 995522515, 974559418, 954108883, 934155160, 914683116, 895678206, 877126444, 859014378, 841329067, 824058054, 807189349, 790711401, 774613086, 758883684, 743512859, 728490646, 713807434, 699453949, 685421240, 671700667, 658283883, 645162828, 632329712, 619777006, 607497430, 595483943, 583729734, 572228213, 560972999, 549957915, 539176979, 528624395, 518294546, 508181991, 498281451, 488587808, 479096098, 469801503, 460699350, 451785101, 443054348, 434502813, 426126339, 417920886, 409882529, 402007452, 394291945, 386732400, 379325306, 372067249, 364954907, 357985044, 351154512, 344460247, 337899261, 331468648, 325165573]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 153).prefactor = (150407494255939/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 153).cutoff/(generalMeanRows 153).c)).2 =
    (196702571987391/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 153).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 153).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 153).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 153

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 153).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 153).criticalRate j.val*(generalMeanRows 153).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 153).c*(generalMeanRows 153).criticalPoint j.val)).2-
      (generalMeanRows 153).J/2-(generalMeanRows 153).error (generalMeanGrid j.val)+
      (generalMeanRows 153).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 153).c)).2-
      (generalMeanRows 153).J/2-(generalMeanRows 153).error 4 := by
  have he : (generalMeanRows 153).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 153) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 153)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0153

/-! Kernel-checked entropy margins for general spectral rectangle 154. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0154
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5359684207, 5187870041, 5023794697, 4867006687, 4717086778, 4573645177, 4436319019, 4304770119, 4178682947, 4057762812, 3941734217, 3830339377, 3723336868, 3620500401, 3521617708, 3426489526, 3334928661, 3246759141, 3161815431, 3079941718, 3000991247, 2924825718, 2851314720, 2780335217, 2711771065, 2645512574, 2581456091, 2519503626, 2459562494, 2401544986, 2345368067, 2290953090, 2238225528, 2187114735, 2137553705, 2089478867, 2042829879, 1997549440, 1953583116, 1910879177, 1869388439, 1829064125, 1789861725, 1751738874, 1714655229, 1678572360, 1643453645, 1609264171, 1575970641, 1543541289, 1511945795, 1481155212, 1451141890, 1421879409, 1393342517, 1365507064, 1338349952, 1311849076, 1285983274, 1260732280, 1236076679, 1211997865, 1188477998, 1165499968, 1143047360, 1121104415, 1099656007, 1078687602, 1058185238, 1038135491, 1018525456, 999342716, 980575324, 962211778, 944241002, 926652326, 909435468, 892580515, 876077906, 859918420, 844093154, 828593518, 813411212, 798538220, 783966794, 769689445, 755698930, 741988243, 728550603, 715379447, 702468419, 689811364, 677402317, 665235497, 653305298, 641606284, 630133182, 618880875, 607844394, 597018917, 586399758, 575982368, 565762322, 555735322, 545897189, 536243856, 526771369, 517475881, 508353645, 499401017, 490614445, 481990471, 473525728, 465216931, 457060883, 449054463, 441194632, 433478423, 425902943, 418465371, 411162951]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 154).prefactor = (1175972338616359/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 154).cutoff/(generalMeanRows 154).c)).2 =
    (216312928564031/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 154).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 154).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 154).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 154

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 154).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 154).criticalRate j.val*(generalMeanRows 154).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 154).c*(generalMeanRows 154).criticalPoint j.val)).2-
      (generalMeanRows 154).J/2-(generalMeanRows 154).error (generalMeanGrid j.val)+
      (generalMeanRows 154).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 154).c)).2-
      (generalMeanRows 154).J/2-(generalMeanRows 154).error 4 := by
  have he : (generalMeanRows 154).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 154) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 154)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0154

/-! Kernel-checked entropy margins for general spectral rectangle 155. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0155
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5382302796, 5212670066, 5050720682, 4896001015, 4748090079, 4606596681, 4471156872, 4341431672, 4217105022, 4097881935, 3983486833, 3873662038, 3768166405, 3666774078, 3569273357, 3475465664, 3385164602, 3298195084, 3214392542, 3133602200, 3055678403, 2980483998, 2907889765, 2837773893, 2770021495, 2704524155, 2641179515, 2579890887, 2520566896, 2463121149, 2407471920, 2353541869, 2301257770, 2250550265, 2201353626, 2153605542, 2107246917, 2062221676, 2018476595, 1975961128, 1934627257, 1894429347, 1855324008, 1817269968, 1780227955, 1744160586, 1709032259, 1674809056, 1641458651, 1608950223, 1577254371, 1546343044, 1516189461, 1486768048, 1458054373, 1430025084, 1402657855, 1375931330, 1349825074, 1324319525, 1299395950, 1275036401, 1251223678, 1227941288, 1205173412, 1182904871, 1161121093, 1139808084, 1118952403, 1098541127, 1078561834, 1059002577, 1039851857, 1021098608, 1002732172, 984742282, 967119044, 949852920, 932934708, 916355533, 900106828, 884180319, 868568018, 853262203, 838255412, 823540428, 809110271, 794958187, 781077636, 767462288, 754106010, 741002858, 728147073, 715533069, 703155429, 691008895, 679088367, 667388890, 655905655, 644633989, 633569349, 622707323, 612043618, 601574060, 591294588, 581201250, 571290199, 561557690, 552000076, 542613803, 533395410, 524341522, 515448849, 506714186, 498134403, 489706449, 481427347, 473294191, 465304145, 457454441, 449742373]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 155).prefactor = (941191771832349/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 155).cutoff/(generalMeanRows 155).c)).2 =
    (453334818365743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 155).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 155).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 155).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 155

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 155).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 155).criticalRate j.val*(generalMeanRows 155).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 155).c*(generalMeanRows 155).criticalPoint j.val)).2-
      (generalMeanRows 155).J/2-(generalMeanRows 155).error (generalMeanGrid j.val)+
      (generalMeanRows 155).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 155).c)).2-
      (generalMeanRows 155).J/2-(generalMeanRows 155).error 4 := by
  have he : (generalMeanRows 155).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 155) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 155)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0155

/-! Kernel-checked entropy margins for general spectral rectangle 156. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0156
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5262276832, 5090846698, 4927223785, 4770948485, 4621594206, 4478764491, 4342090442, 4211228418, 4085857958, 3965679922, 3850414802, 3739801196, 3633594431, 3531565299, 3433498918, 3339193680, 3248460303, 3161120951, 3077008436, 2995965477, 2917844026, 2842504643, 2769815921, 2699653952, 2631901841, 2566449247, 2503191965, 2442031534, 2382874878, 2325633967, 2270225503, 2216570635, 2164594682, 2114226884, 2065400167, 2018050922, 1972118801, 1927546524, 1884279704, 1842266674, 1801458336, 1761808011, 1723271302, 1685805966, 1649371794, 1613930496, 1579445596, 1545882330, 1513207558, 1481389668, 1450398499, 1420205264, 1390782469, 1362103854, 1334144321, 1306879877, 1280287574, 1254345457, 1229032509, 1204328609, 1180214480, 1156671652, 1133682416, 1111229791, 1089297484, 1067869858, 1046931901, 1026469190, 1006467870, 986914621, 967796636, 949101593, 930817636, 912933350, 895437743, 878320223, 861570585, 845178986, 829135937, 813432280, 798059177, 783008093, 768270788, 753839298, 739705926, 725863230, 712304013, 699021311, 686008384, 673258709, 660765964, 648524030, 636526972, 624769042, 613244661, 601948422, 590875076, 580019529, 569376838, 558942201, 548710952, 538678561, 528840622, 519192854, 509731093, 500451289, 491349502, 482421898, 473664745, 465074409, 456647352, 448380127, 440269377, 432311830, 424504296, 416843667, 409326910, 401951070, 394713262, 387610673, 380640558]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 156).prefactor = (4770530028830473/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 156).cutoff/(generalMeanRows 156).c)).2 =
    (436527700049359/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 156).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 156).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 156).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 156

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 156).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 156).criticalRate j.val*(generalMeanRows 156).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 156).c*(generalMeanRows 156).criticalPoint j.val)).2-
      (generalMeanRows 156).J/2-(generalMeanRows 156).error (generalMeanGrid j.val)+
      (generalMeanRows 156).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 156).c)).2-
      (generalMeanRows 156).J/2-(generalMeanRows 156).error 4 := by
  have he : (generalMeanRows 156).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 156) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 156)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0156

/-! Kernel-checked entropy margins for general spectral rectangle 157. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0157
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5245559431, 5071951810, 4906210213, 4747876892, 4596526743, 4451764465, 4313222012, 4180556316, 4053447246, 3931595763, 3814722261, 3702565062, 3594879054, 3491434447, 3392015649, 3296420234, 3204458001, 3115950111, 3030728297, 2948634138, 2869518392, 2793240380, 2719667417, 2648674289, 2580142771, 2513961177, 2450023941, 2388231239, 2328488626, 2270706705, 2214800817, 2160690757, 2108300501, 2057557961, 2008394749, 1960745960, 1914549968, 1869748239, 1826285150, 1784107826, 1743165979, 1703411770, 1664799663, 1627286307, 1590830405, 1555392610, 1520935414, 1487423048, 1454821393, 1423097886, 1392221441, 1362162370, 1332892308, 1304384147, 1276611968, 1249550980, 1223177465, 1197468717, 1172402999, 1147959487, 1124118229, 1100860098, 1078166754, 1056020603, 1034404763, 1013303027, 992699832, 972580226, 952929843, 933734870, 914982024, 896658527, 878752082, 861250851, 844143434, 827418846, 811066505, 795076208, 779438114, 764142733, 749180905, 734543788, 720222844, 706209827, 692496767, 679075962, 665939966, 653081574, 640493819, 628169956, 616103457, 604288000, 592717460, 581385904, 570287581, 559416916, 548768501, 538337091, 528117598, 518105081, 508294747, 498681938, 489262131, 480030933, 470984073, 462117399, 453426877, 444908580, 436558692, 428373498, 420349382, 412482826, 404770405, 397208782, 389794707, 382525017, 375396626, 368406529, 361551796, 354829570, 348237066]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 157).prefactor = (4770534057410601/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 157).cutoff/(generalMeanRows 157).c)).2 =
    (415958804642851/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 157).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 157).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 157).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 157

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 157).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 157).criticalRate j.val*(generalMeanRows 157).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 157).c*(generalMeanRows 157).criticalPoint j.val)).2-
      (generalMeanRows 157).J/2-(generalMeanRows 157).error (generalMeanGrid j.val)+
      (generalMeanRows 157).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 157).c)).2-
      (generalMeanRows 157).J/2-(generalMeanRows 157).error 4 := by
  have he : (generalMeanRows 157).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 157) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 157)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0157

/-! Kernel-checked entropy margins for general spectral rectangle 158. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0158
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4960452223, 4786176522, 4619908584, 4461184051, 4309571574, 4164669930, 4026105457, 3893529752, 3766617606, 3645065143, 3528588143, 3416920521, 3309812953, 3207031619, 3108357069, 3013583176, 2922516191, 2834973870, 2750784676, 2669787044, 2591828709, 2516766083, 2444463685, 2374793606, 2307635025, 2242873754, 2180401820, 2120117074, 2061922830, 2005727529, 1951444431, 1898991316, 1848290222, 1799267187, 1751852015, 1705978056, 1661582002, 1618603692, 1576985934, 1536674338, 1497617156, 1459765136, 1423071383, 1387491229, 1352982111, 1319503458, 1287016581, 1255484574, 1224872219, 1195145894, 1166273492, 1138224341, 1110969129, 1084479832, 1058729653, 1033692952, 1009345194, 985662890, 962623546, 940205611, 918388432, 897152212, 876477965, 856347477, 836743269, 817648563, 799047247, 780923845, 763263486, 746051874, 729275264, 712920437, 696974672, 681425728, 666261818, 651471591, 637044113, 622968846, 609235632, 595834678, 582756536, 569992092, 557532549, 545369416, 533494492, 521899857, 510577856, 499521094, 488722419, 478174916, 467871897, 457806889, 447973631, 438366060, 428978304, 419804678, 410839674, 402077954, 393514345, 385143833, 376961552, 368962787, 361142961, 353497634, 346022495, 338713362, 331566170, 324576976, 317741946, 311057357, 304519590, 298125129, 291870555, 285752542, 279767859, 273913361, 268185988, 262582765, 257100794, 251737257, 246489408]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 158).prefactor = (2419061491243417/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 158).cutoff/(generalMeanRows 158).c)).2 =
    (95858903234323/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 158).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 158).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 158).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 158

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 158).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 158).criticalRate j.val*(generalMeanRows 158).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 158).c*(generalMeanRows 158).criticalPoint j.val)).2-
      (generalMeanRows 158).J/2-(generalMeanRows 158).error (generalMeanGrid j.val)+
      (generalMeanRows 158).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 158).c)).2-
      (generalMeanRows 158).J/2-(generalMeanRows 158).error 4 := by
  have he : (generalMeanRows 158).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 158) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 158)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0158

/-! Kernel-checked entropy margins for general spectral rectangle 159. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0159
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5056512760, 4883866020, 4719158736, 4561925099, 4411732675, 4268179493, 4130891444, 3999519949, 3873739870, 3753247622, 3637759471, 3527009998, 3420750696, 3318748701, 3220785641, 3126656574, 3036169023, 2949142100, 2865405687, 2784799698, 2707173392, 2632384743, 2560299860, 2490792450, 2423743323, 2359039928, 2296575938, 2236250846, 2177969604, 2121642284, 2067183761, 2014513418, 1963554875, 1914235733, 1866487333, 1820244541, 1775445537, 1732031618, 1689947025, 1649138769, 1609556470, 1571152215, 1533880417, 1497697680, 1462562685, 1428436067, 1395280314, 1363059664, 1331740008, 1301288802, 1271674987, 1242868902, 1214842218, 1187567863, 1161019959, 1135173758, 1110005584, 1085492780, 1061613653, 1038347427, 1015674199, 993574888, 972031203, 951025599, 930541240, 910561966, 891072260, 872057218, 853502516, 835394387, 817719592, 800465394, 783619540, 767170231, 751106107, 735416225, 720090041, 705117388, 690488465, 676193816, 662224319, 648571167, 635225857, 622180176, 609426190, 596956230, 584762881, 572838973, 561177572, 549771964, 538615654, 527702350, 517025962, 506580587, 496360507, 486360176, 476574221, 466997427, 457624739, 448451248, 439472192, 430682947, 422079022, 413656057, 405409814, 397336175, 389431139, 381690814, 374111416, 366689267, 359420785, 352302488, 345330984, 338502975, 331815248, 325264674, 318848205, 312562873, 306405788, 300374129, 294465151]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 159).prefactor = (4835987189235029/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 159).cutoff/(generalMeanRows 159).c)).2 =
    (41183508745899/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 159).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 159).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 159).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 159

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 159).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 159).criticalRate j.val*(generalMeanRows 159).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 159).c*(generalMeanRows 159).criticalPoint j.val)).2-
      (generalMeanRows 159).J/2-(generalMeanRows 159).error (generalMeanGrid j.val)+
      (generalMeanRows 159).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 159).c)).2-
      (generalMeanRows 159).J/2-(generalMeanRows 159).error 4 := by
  have he : (generalMeanRows 159).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 159) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 159)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0159

/-! Kernel-checked entropy margins for general spectral rectangle 160. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0160
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5294549380, 5122104783, 4957545098, 4800403703, 4650247606, 4506674511, 4369310194, 4237806152, 4111837493, 3991101028, 3875313560, 3764210325, 3657543582, 3555081328, 3456606133, 3361914075, 3270813759, 3183125434, 3098680164, 3017319088, 2938892719, 2863260314, 2790289285, 2719854657, 2651838566, 2586129802, 2522623371, 2461220107, 2401826294, 2344353332, 2288717412, 2234839223, 2182643678, 2132059654, 2083019752, 2035460080, 1989320037, 1944542123, 1901071756, 1858857103, 1817848920, 1778000401, 1739267044, 1701606514, 1664978528, 1629344731, 1594668599, 1560915326, 1528051742, 1496046212, 1464868561, 1434489991, 1404883005, 1376021346, 1347879920, 1320434743, 1293662880, 1267542389, 1242052271, 1217172422, 1192883586, 1169167311, 1146005911, 1123382425, 1101280584, 1079684771, 1058579994, 1037951853, 1017786514, 998070676, 978791552, 959936837, 941494694, 923453725, 905802952, 888531800, 871630075, 855087949, 838895943, 823044910, 807526021, 792330751, 777450865, 762878405, 748605681, 734625254, 720929930, 707512747, 694366967, 681486064, 668863720, 656493811, 644370401, 632487736, 620840236, 609422488, 598229237, 587255384, 576495977, 565946207, 555601402, 545457019, 535508646, 525751991, 516182879, 506797251, 497591153, 488560742, 479702272, 471012098, 462486668, 454122524, 445916293, 437864690, 429964513, 422212638, 414606020, 407141687, 399816742, 392628355, 385573766]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 160).prefactor = (4834665085714413/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 160).cutoff/(generalMeanRows 160).c)).2 =
    (221359835148641/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 160).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 160).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 160).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 160

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 160).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 160).criticalRate j.val*(generalMeanRows 160).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 160).c*(generalMeanRows 160).criticalPoint j.val)).2-
      (generalMeanRows 160).J/2-(generalMeanRows 160).error (generalMeanGrid j.val)+
      (generalMeanRows 160).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 160).c)).2-
      (generalMeanRows 160).J/2-(generalMeanRows 160).error 4 := by
  have he : (generalMeanRows 160).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 160) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 160)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0160

/-! Kernel-checked entropy margins for general spectral rectangle 161. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0161
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5330184063, 5156578837, 4990911592, 4832712565, 4681545850, 4537006444, 4398717604, 4266328481, 4139511996, 4017962921, 3901396152, 3789545143, 3682160484, 3579008613, 3479870637, 3384541258, 3292827797, 3204549290, 3119535666, 3037626993, 2958672780, 2882531335, 2809069179, 2738160494, 2669686625, 2603535611, 2539601754, 2477785218, 2417991658, 2360131877, 2304121502, 2249880690, 2197333846, 2146409368, 2097039406, 2049159636, 2002709049, 1957629760, 1913866818, 1871368042, 1830083855, 1789967138, 1750973088, 1713059087, 1676184577, 1640310949, 1605401431, 1571420984, 1538336213, 1506115272, 1474727781, 1444144749, 1414338496, 1385282584, 1356951754, 1329321859, 1302369809, 1276073515, 1250411838, 1225364536, 1200912225, 1177036329, 1153719043, 1130943291, 1108692694, 1086951531, 1065704710, 1044937733, 1024636672, 1004788138, 985379256, 966397641, 947831374, 929668981, 911899410, 894512016, 877496534, 860843073, 844542087, 828584370, 812961032, 797663491, 782683456, 768012918, 753644132, 739569610, 725782110, 712274624, 699040367, 686072770, 673365472, 660912307, 648707301, 636744661, 625018769, 613524174, 602255587, 591207875, 580376053, 569755278, 559340847, 549128189, 539112859, 529290537, 519657021, 510208222, 500940164, 491848974, 482930883, 474182220, 465599410, 457178971, 448917509, 440811715, 432858366, 425054318, 417396504, 409881933, 402507687, 395270919, 388168850]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 161).prefactor = (1216801135435723/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 161).cutoff/(generalMeanRows 161).c)).2 =
    (221359835148641/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 161).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 161).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 161).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 161

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 161).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 161).criticalRate j.val*(generalMeanRows 161).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 161).c*(generalMeanRows 161).criticalPoint j.val)).2-
      (generalMeanRows 161).J/2-(generalMeanRows 161).error (generalMeanGrid j.val)+
      (generalMeanRows 161).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 161).c)).2-
      (generalMeanRows 161).J/2-(generalMeanRows 161).error 4 := by
  have he : (generalMeanRows 161).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 161) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 161)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0161

/-! Kernel-checked entropy margins for general spectral rectangle 162. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0162
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5091085157, 4917257997, 4751424575, 4593115900, 4441896581, 4297361897, 4159135181, 4026865473, 3900225410, 3778909332, 3662631566, 3551124877, 3444139058, 3341439655, 3242806802, 3148034155, 3056927923, 2969305979, 2884997043, 2803839935, 2725682882, 2650382888, 2577805146, 2507822500, 2440314944, 2375169160, 2312278091, 2251540543, 2192860821, 2136148380, 2081317513, 2028287053, 1976980096, 1927323748, 1879248883, 1832689920, 1787584616, 1743873867, 1701501534, 1660414263, 1620561332, 1581894500, 1544367867, 1507937741, 1472562521, 1438202572, 1404820127, 1372379178, 1340845382, 1310185976, 1280369685, 1251366647, 1223148339, 1195687504, 1168958087, 1142935170, 1117594916, 1092914513, 1068872119, 1045446818, 1022618568, 1000368160, 978677177, 957527953, 936903538, 916787662, 897164701, 878019649, 859338085, 841106147, 823310505, 805938337, 788977304, 772415528, 756241571, 740444414, 725013442, 709938418, 695209474, 680817090, 666752080, 653005579, 639569024, 626434147, 613592960, 601037740, 588761022, 576755589, 565014456, 553530866, 542298277, 531310358, 520560973, 510044181, 499754223, 489685519, 479832655, 470190383, 460753611, 451517399, 442476952, 433627613, 424964862, 416484307, 408181683, 400052843, 392093758, 384300511, 376669292, 369196395, 361878217, 354711251, 347692082, 340817389, 334083936, 327488574, 321028234, 314699929, 308500746, 302427847, 296478468]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 162).prefactor = (4869051808477883/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 162).cutoff/(generalMeanRows 162).c)).2 =
    (41183508745899/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 162).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 162).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 162).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 162

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 162).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 162).criticalRate j.val*(generalMeanRows 162).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 162).c*(generalMeanRows 162).criticalPoint j.val)).2-
      (generalMeanRows 162).J/2-(generalMeanRows 162).error (generalMeanGrid j.val)+
      (generalMeanRows 162).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 162).c)).2-
      (generalMeanRows 162).J/2-(generalMeanRows 162).error 4 := by
  have he : (generalMeanRows 162).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 162) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 162)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0162

/-! Kernel-checked entropy margins for general spectral rectangle 163. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0163
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5125893932, 4950878281, 4783911023, 4624519960, 4472266723, 4326743826, 4187572027, 4054397964, 3926892038, 3804746497, 3687673716, 3575404633, 3467687331, 3364285752, 3264978526, 3169557899, 3077828755, 2989607723, 2904722350, 2823010354, 2744318925, 2668504090, 2595430120, 2524968988, 2456999869, 2391408670, 2328087602, 2266934780, 2207853852, 2150753657, 2095547900, 2042154860, 1990497107, 1940501249, 1892097687, 1845220391, 1799806692, 1755797085, 1713135043, 1671766850, 1631641436, 1592710231, 1554927021, 1518247816, 1482630727, 1448035853, 1414425165, 1381762411, 1350013013, 1319143982, 1289123830, 1259922493, 1231511251, 1203862661, 1176950489, 1150749648, 1125236138, 1100386990, 1076180213, 1052594749, 1029610417, 1007207879, 985368590, 964074764, 943309336, 923055924, 903298797, 884022846, 865213553, 846856959, 828939645, 811448700, 794371701, 777696689, 761412147, 745506982, 729970505, 714792410, 699962761, 685471973, 671310799, 657470310, 643941886, 630717204, 617788218, 605147156, 592786500, 580698983, 568877574, 557315468, 546006080, 534943034, 524120153, 513531456, 503171144, 493033597, 483113367, 473405169, 463903876, 454604515, 445502256, 436592412, 427870432, 419331894, 410972503, 402788085, 394774582, 386928051, 379244655, 371720665, 364352452, 357136483, 350069323, 343147626, 336368135, 329727679, 323223169, 316851596, 310610028, 304495608, 298505551]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 163).prefactor = (153198203037113/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 163).cutoff/(generalMeanRows 163).c)).2 =
    (41183508745899/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 163).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 163).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 163).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 163

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 163).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 163).criticalRate j.val*(generalMeanRows 163).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 163).c*(generalMeanRows 163).criticalPoint j.val)).2-
      (generalMeanRows 163).J/2-(generalMeanRows 163).error (generalMeanGrid j.val)+
      (generalMeanRows 163).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 163).c)).2-
      (generalMeanRows 163).J/2-(generalMeanRows 163).error 4 := by
  have he : (generalMeanRows 163).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 163) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 163)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0163

/-! Kernel-checked entropy margins for general spectral rectangle 164. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0164
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5096111890, 4922157255, 4756169879, 4597684708, 4446269900, 4301523931, 4163073008, 4030568748, 3903686103, 3782121480, 3665591054, 3553829232, 3446587270, 3343632007, 3244744716, 3149720057, 3058365114, 2970498523, 2885949663, 2804557918, 2726171996, 2650649303, 2577855366, 2507663300, 2439953312, 2374612248, 2311533171, 2250614964, 2191761971, 2134883659, 2079894298, 2026712677, 1975261825, 1925468759, 1877264249, 1830582594, 1785361418, 1741541476, 1699066473, 1657882898, 1617939861, 1579188950, 1541584089, 1505081409, 1469639127, 1435217428, 1401778364, 1369285744, 1337705047, 1307003329, 1277149137, 1248112437, 1219864532, 1192377996, 1165626606, 1139585284, 1114230032, 1089537881, 1065486841, 1042055845, 1019224708, 996974081, 975285412, 954140904, 933523478, 913416741, 893804952, 874672987, 856006315, 837790967, 820013510, 802661022, 785721068, 769181679, 753031328, 737258913, 721853735, 706805481, 692104208, 677740324, 663704576, 649988032, 636582067, 623478354, 610668848, 598145771, 585901609, 573929093, 562221192, 550771106, 539572250, 528618252, 517902939, 507420335, 497164646, 487130259, 477311732, 467703786, 458301304, 449099319, 440093011, 431277703, 422648853, 414202049, 405933007, 397837564, 389911674, 382151404, 374552931, 367112537, 359826605, 352691617, 345704149, 338860870, 332158536, 325593989, 319164154, 312866036, 306696718, 300653356, 294733180]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 164).prefactor = (4837140140634371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 164).cutoff/(generalMeanRows 164).c)).2 =
    (101420305471153/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 164).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 164).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 164).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 164

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 164).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 164).criticalRate j.val*(generalMeanRows 164).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 164).c*(generalMeanRows 164).criticalPoint j.val)).2-
      (generalMeanRows 164).J/2-(generalMeanRows 164).error (generalMeanGrid j.val)+
      (generalMeanRows 164).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 164).c)).2-
      (generalMeanRows 164).J/2-(generalMeanRows 164).error 4 := by
  have he : (generalMeanRows 164).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 164) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 164)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0164

/-! Kernel-checked entropy margins for general spectral rectangle 165. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0165
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5042311195, 4867614280, 4700947406, 4541842249, 4389863906, 4244607975, 4105697958, 3972782928, 3845535432, 3723649613, 3606839503, 3494837484, 3387392890, 3284270740, 3185250582, 3090125432, 2998700818, 2910793891, 2826232616, 2744855033, 2666508566, 2591049397, 2518341885, 2448258029, 2380676970, 2315484536, 2252572812, 2191839751, 2133188804, 2076528580, 2021772533, 1968838666, 1917649256, 1868130598, 1820212770, 1773829408, 1728917499, 1685417187, 1643271592, 1602426636, 1562830891, 1524435426, 1487193665, 1451061261, 1415995971, 1381957538, 1348907588, 1316809524, 1285628433, 1255330993, 1225885391, 1197261245, 1169429524, 1142362481, 1116033587, 1090417465, 1065489836, 1041227457, 1017608076, 994610374, 972213927, 950399152, 929147277, 908440289, 888260907, 868592542, 849419263, 830725769, 812497354, 794719885, 777379770, 760463937, 743959806, 727855268, 712138666, 696798769, 681824758, 667206206, 652933059, 638995620, 625384536, 612090781, 599105639, 586420697, 574027826, 561919175, 550087153, 538524421, 527223885, 516178679, 505382162, 494827906, 484509685, 474421473, 464557432, 454911904, 445479406, 436254625, 427232405, 418407749, 409775806, 401331871, 393071376, 384989887, 377083098, 369346827, 361777010, 354369701, 347121061, 340027361, 333084974, 326290373, 319640129, 313130903, 306759447, 300522603, 294417292, 288440520, 282589371, 276861003, 271252651]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 165).prefactor = (4870742327589027/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 165).cutoff/(generalMeanRows 165).c)).2 =
    (397584011651991/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 165).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 165).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 165).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 165

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 165).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 165).criticalRate j.val*(generalMeanRows 165).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 165).c*(generalMeanRows 165).criticalPoint j.val)).2-
      (generalMeanRows 165).J/2-(generalMeanRows 165).error (generalMeanGrid j.val)+
      (generalMeanRows 165).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 165).c)).2-
      (generalMeanRows 165).J/2-(generalMeanRows 165).error 4 := by
  have he : (generalMeanRows 165).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 165) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 165)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0165

/-! Kernel-checked entropy margins for general spectral rectangle 166. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0166
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4910130669, 4735167047, 4568274026, 4408983868, 4256862055, 4111504389, 3972534413, 3839601093, 3712376740, 3590555140, 3473849863, 3361992734, 3254732453, 3151833327, 3053074128, 2958247045, 2867156730, 2779619415, 2695462118, 2614521897, 2536645176, 2461687120, 2389511054, 2319987935, 2252995861, 2188419607, 2126150214, 2066084588, 2008125142, 1952179457, 1898159966, 1845983663, 1795571830, 1746849784, 1699746637, 1654195080, 1610131170, 1567494139, 1526226216, 1486272454, 1447580571, 1410100805, 1373785772, 1338590334, 1304471481, 1271388210, 1239301421, 1208173811, 1177969785, 1148655359, 1120198078, 1092566937, 1065732306, 1039665855, 1014340495, 989730308, 965810490, 942557295, 919947985, 897960775, 876574788, 855770012, 835527255, 815828109, 796654909, 777990697, 759819192, 742124754, 724892358, 708107560, 691756476, 675825752, 660302540, 645174477, 630429663, 616056636, 602044359, 588382195, 575059895, 562067576, 549395707, 537035096, 524976873, 513212475, 501733637, 490532375, 479600978, 468931997, 458518228, 448352710, 438428710, 428739717, 419279428, 410041748, 401020773, 392210788, 383606258, 375201823, 366992286, 358972613, 351137925, 343483487, 336004712, 328697148, 321556476, 314578504, 307759165, 301094509, 294580702, 288214018, 281990841, 275907656, 269961046, 264147693, 258464369, 252907937, 247475346, 242163629, 236969900, 231891350, 226925248]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 166).prefactor = (4872275701495047/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 166).cutoff/(generalMeanRows 166).c)).2 =
    (75093488657623/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 166).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 166).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 166).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 166

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 166).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 166).criticalRate j.val*(generalMeanRows 166).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 166).c*(generalMeanRows 166).criticalPoint j.val)).2-
      (generalMeanRows 166).J/2-(generalMeanRows 166).error (generalMeanGrid j.val)+
      (generalMeanRows 166).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 166).c)).2-
      (generalMeanRows 166).J/2-(generalMeanRows 166).error 4 := by
  have he : (generalMeanRows 166).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 166) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 166)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0166

/-! Kernel-checked entropy margins for general spectral rectangle 167. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0167
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4860823206, 4685203577, 4517717290, 4357893176, 4205293499, 4059511046, 3920166524, 3786906230, 3659399961, 3537339133, 3420435075, 3308417500, 3201033102, 3098044294, 2999228051, 2904374859, 2813287749, 2725781420, 2641681427, 2560823440, 2483052562, 2408222696, 2336195972, 2266842203, 2200038395, 2135668288, 2073621927, 2013795274, 1956089838, 1900412335, 1846674374, 1794792161, 1744686225, 1696281161, 1649505394, 1604290954, 1560573269, 1518290969, 1477385705, 1437801978, 1399486980, 1362390442, 1326464497, 1291663546, 1257944133, 1225264834, 1193586142, 1162870368, 1133081545, 1104185334, 1076148941, 1048941036, 1022531678, 996892242, 971995354, 947814825, 924325593, 901503664, 879326063, 857770781, 836816725, 816443677, 796632252, 777363852, 758620636, 740385476, 722641931, 705374207, 688567132, 672206126, 656277172, 640766790, 625662015, 610950371, 596619852, 582658897, 569056371, 555801551, 542884100, 530294057, 518021817, 506058116, 494394018, 483020899, 471930436, 461114592, 450565606, 440275980, 430238470, 420446074, 410892022, 401569770, 392472985, 383595542, 374931515, 366475166, 358220939, 350163456, 342297507, 334618045, 327120176, 319799162, 312650405, 305669449, 298851972, 292193781, 285690808, 279339105, 273134841, 267074295, 261153857, 255370017, 249719370, 244198605, 238804507, 233533948, 228383892, 223351385, 218433555, 213627611, 208930835]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 167).prefactor = (2453334753716513/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 167).cutoff/(generalMeanRows 167).c)).2 =
    (183781131890501/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 167).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 167).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 167).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 167

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 167).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 167).criticalRate j.val*(generalMeanRows 167).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 167).c*(generalMeanRows 167).criticalPoint j.val)).2-
      (generalMeanRows 167).J/2-(generalMeanRows 167).error (generalMeanGrid j.val)+
      (generalMeanRows 167).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 167).c)).2-
      (generalMeanRows 167).J/2-(generalMeanRows 167).error 4 := by
  have he : (generalMeanRows 167).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 167) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 167)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0167

/-! Kernel-checked entropy margins for general spectral rectangle 168. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0168
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4903861391, 4728997949, 4562233683, 4403096853, 4251149325, 4105983640, 3967220402, 3834505927, 3707510147, 3585924712, 3469461279, 3357849962, 3250837935, 3148188148, 3049678169, 2955099125, 2864254729, 2776960394, 2693042420, 2612337247, 2534690764, 2459957681, 2388000940, 2318691179, 2251906232, 2187530669, 2125455365, 2065577110, 2007798234, 1952026270, 1898173635, 1846157333, 1795898680, 1747323048, 1700359624, 1654941186, 1611003897, 1568487107, 1527333169, 1487487274, 1448897283, 1411513583, 1375288945, 1340178390, 1306139069, 1273130141, 1241112672, 1210049526, 1179905271, 1150646089, 1122239689, 1094655229, 1067863237, 1041835545, 1016545217, 991966489, 968074707, 944846274, 922258593, 900290021, 878919817, 858128102, 837895816, 818204674, 799037135, 780376358, 762206178, 744511066, 727276104, 710486952, 694129825, 678191466, 662659121, 647520516, 632763836, 618377703, 604351159, 590673645, 577334983, 564325362, 551635318, 539255723, 527177768, 515392950, 503893060, 492670169, 481716616, 471025001, 460588167, 450399198, 440451403, 430738309, 421253655, 411991379, 402945614, 394110676, 385481062, 377051440, 368816642, 360771659, 352911636, 345231864, 337727776, 330394941, 323229059, 316225957, 309381584, 302692006, 296153405, 289762069, 283514394, 277406877, 271436113, 265598793, 259891701, 254311708, 248855770, 243520928, 238304303, 233203092, 228214570]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 168).prefactor = (490457793903321/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 168).cutoff/(generalMeanRows 168).c)).2 =
    (381583670305549/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 168).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 168).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 168).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 168

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 168).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 168).criticalRate j.val*(generalMeanRows 168).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 168).c*(generalMeanRows 168).criticalPoint j.val)).2-
      (generalMeanRows 168).J/2-(generalMeanRows 168).error (generalMeanGrid j.val)+
      (generalMeanRows 168).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 168).c)).2-
      (generalMeanRows 168).J/2-(generalMeanRows 168).error 4 := by
  have he : (generalMeanRows 168).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 168) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 168)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0168

/-! Kernel-checked entropy margins for general spectral rectangle 169. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0169
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4853586287, 4678086004, 4510747010, 4351094166, 4198686154, 4053112525, 3913991073, 3780965474, 3653703168, 3531893455, 3415245775, 3303488146, 3196365758, 3093639682, 2995085706, 2900493267, 2809664476, 2722413221, 2638564357, 2557952944, 2480423563, 2405829675, 2334033034, 2264903143, 2198316757, 2134157415, 2072315009, 2012685389, 1955169989, 1899675486, 1846113478, 1794400186, 1744456181, 1696206117, 1649578500, 1604505454, 1560922515, 1518768436, 1477984998, 1438516843, 1400311309, 1363318282, 1327490051, 1292781180, 1259148378, 1226550387, 1194947868, 1164303301, 1134580885, 1105746450, 1077767368, 1050612475, 1024251991, 998657453, 973801643, 949658529, 926203199, 903411811, 881261533, 859730498, 838797753, 818443214, 798647627, 779392522, 760660180, 742433595, 724696440, 707433034, 690628315, 674267806, 658337591, 642824290, 627715030, 612997427, 598659560, 584689953, 571077553, 557811711, 544882168, 532279031, 519992765, 508014171, 496334376, 484944815, 473837221, 463003614, 452436283, 442127782, 432070912, 422258717, 412684471, 403341669, 394224019, 385325433, 376640018, 368162069, 359886064, 351806654, 343918657, 336217051, 328696971, 321353700, 314182663, 307179426, 300339686, 293659269, 287134125, 280760323, 274534046, 268451588, 262509353, 256703844, 251031666, 245489520, 240074200, 234782590, 229611660, 224558465, 219620140, 214793901, 210077036]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 169).prefactor = (4938648596498067/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 169).cutoff/(generalMeanRows 169).c)).2 =
    (373678490798437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 169).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 169).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 169).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 169

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 169).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 169).criticalRate j.val*(generalMeanRows 169).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 169).c*(generalMeanRows 169).criticalPoint j.val)).2-
      (generalMeanRows 169).J/2-(generalMeanRows 169).error (generalMeanGrid j.val)+
      (generalMeanRows 169).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 169).c)).2-
      (generalMeanRows 169).J/2-(generalMeanRows 169).error 4 := by
  have he : (generalMeanRows 169).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 169) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 169)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0169

/-! Kernel-checked entropy margins for general spectral rectangle 170. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0170
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5243211813, 5076207539, 4916761041, 4764426274, 4618789336, 4479465656, 4346097490, 4218351670, 4095917592, 3978505389, 3865844297, 3757681161, 3653779093, 3553916244, 3457884687, 3365489397, 3276547324, 3190886536, 3108345441, 3028772067, 2952023401, 2877964783, 2806469344, 2737417490, 2670696421, 2606199692, 2543826802, 2483482814, 2425078001, 2368527525, 2313751123, 2260672834, 2209220729, 2159326672, 2110926083, 2063957734, 2018363542, 1974088389, 1931079946, 1889288510, 1848666853, 1809170080, 1770755496, 1733382479, 1697012367, 1661608345, 1627135343, 1593559942, 1560850278, 1528975964, 1497908002, 1467618715, 1438081670, 1409271619, 1381164428, 1353737023, 1326967336, 1300834247, 1275317541, 1250397856, 1226056645, 1202276128, 1179039261, 1156329691, 1134131729, 1112430311, 1091210971, 1070459810, 1050163469, 1030309104, 1010884358, 991877342, 973276610, 955071140, 937250311, 919803888, 902722005, 885995141, 869614114, 853570059, 837854417, 822458919, 807375574, 792596661, 778114711, 763922499, 750013034, 736379548, 723015490, 709914510, 697070458, 684477372, 672129471, 660021149, 648146964, 636501637, 625080043, 613877204, 602888285, 592108588, 581533547, 571158721, 560979795, 550992568, 541192954, 531576976, 522140764, 512880548, 503792655, 494873510, 486119628, 477527611, 469094148, 460816012, 452690051, 444713196, 436882450, 429194887, 421647653, 414237963, 406963094]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 170).prefactor = (2340074444529091/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 170).cutoff/(generalMeanRows 170).c)).2 =
    (44855030002659/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 170).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 170).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 170).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 170

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 170).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 170).criticalRate j.val*(generalMeanRows 170).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 170).c*(generalMeanRows 170).criticalPoint j.val)).2-
      (generalMeanRows 170).J/2-(generalMeanRows 170).error (generalMeanGrid j.val)+
      (generalMeanRows 170).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 170).c)).2-
      (generalMeanRows 170).J/2-(generalMeanRows 170).error 4 := by
  have he : (generalMeanRows 170).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 170) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 170)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0170

/-! Kernel-checked entropy margins for general spectral rectangle 171. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0171
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5277960486, 5109849414, 4949346206, 4796001862, 4649399734, 4509152706, 4374900660, 4246308222, 4123062729, 4004872393, 3891464654, 3782584682, 3677994017, 3577469341, 3480801347, 3387793720, 3298262195, 3212033703, 3128945578, 3048844842, 2971587535, 2897038103, 2825068838, 2755559352, 2688396098, 2623471926, 2560685668, 2499941758, 2441149876, 2384224619, 2329085194, 2275655135, 2223862039, 2173637316, 2124915959, 2077636333, 2031739972, 1987171391, 1943877916, 1901809513, 1860918641, 1821160109, 1782490937, 1744870236, 1708259085, 1672620428, 1637918961, 1604121044, 1571194601, 1539109044, 1507835184, 1477345158, 1447612361, 1418611375, 1390317907, 1362708731, 1335761631, 1309455349, 1283769534, 1258684698, 1234182168, 1210244050, 1186853183, 1163993109, 1141648033, 1119802792, 1098442823, 1077554137, 1057123285, 1037137337, 1017583856, 998450874, 979726869, 961400744, 943461810, 925899764, 908704672, 891866953, 875377364, 859226979, 843407183, 827909653, 812726346, 797849488, 783271561, 768985291, 754983643, 741259804, 727807176, 714619372, 701690198, 689013653, 676583918, 664395349, 652442470, 640719965, 629222676, 617945592, 606883845, 596032707, 585387581, 574943998, 564697612, 554644196, 544779636, 535099930, 525601181, 516279594, 507131472, 498153217, 489341320, 480692360, 472203006, 463870007, 455690193, 447660473, 439777829, 432039318, 424442066, 416983269, 409660187]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 171).prefactor = (2355582969676177/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 171).cutoff/(generalMeanRows 171).c)).2 =
    (44855030002659/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 171).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 171).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 171).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 171

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 171).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 171).criticalRate j.val*(generalMeanRows 171).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 171).c*(generalMeanRows 171).criticalPoint j.val)).2-
      (generalMeanRows 171).J/2-(generalMeanRows 171).error (generalMeanGrid j.val)+
      (generalMeanRows 171).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 171).c)).2-
      (generalMeanRows 171).J/2-(generalMeanRows 171).error 4 := by
  have he : (generalMeanRows 171).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 171) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 171)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0171

/-! Kernel-checked entropy margins for general spectral rectangle 172. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0172
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4929966858, 4754070945, 4586355125, 4426340541, 4273582558, 4127667778, 3988211375, 3854854706, 3727263167, 3605124264, 3488145866, 3376054627, 3268594557, 3165525720, 3066623046, 2971675252, 2880483855, 2792862264, 2708634951, 2627636691, 2549711857, 2474713777, 2402504139, 2332952438, 2265935473, 2201336872, 2139046659, 2078960851, 2020981081, 1965014249, 1910972204, 1858771436, 1808332799, 1759581251, 1712445605, 1666858310, 1622755227, 1580075444, 1538761077, 1498757107, 1460011213, 1422473617, 1386096947, 1350836101, 1316648118, 1283492067, 1251328931, 1220121505, 1189834300, 1160433446, 1131886614, 1104162927, 1077232889, 1051068310, 1025642238, 1000928899, 976903633, 953542837, 930823915, 908725224, 887226030, 866306459, 845947455, 826130745, 806838793, 788054772, 769762525, 751946533, 734591889, 717684264, 701209884, 685155500, 669508368, 654256225, 639387262, 624890113, 610753824, 596967844, 583522001, 570406490, 557611851, 545128960, 532949012, 521063507, 509464235, 498143270, 487092951, 476305876, 465774890, 455493071, 445453728, 435650385, 426076776, 416726834, 407594686, 398674645, 389961200, 381449011, 373132905, 365007865, 357069026, 349311671, 341731224, 334323243, 327083420, 320007572, 313091635, 306331667, 299723836, 293264421, 286949804, 280776471, 274741006, 268840087, 263070485, 257429057, 251912750, 246518589, 241243684, 236085218, 231040451]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 172).prefactor = (4969608276305901/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 172).cutoff/(generalMeanRows 172).c)).2 =
    (387737535879929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 172).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 172).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 172).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 172

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 172).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 172).criticalRate j.val*(generalMeanRows 172).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 172).c*(generalMeanRows 172).criticalPoint j.val)).2-
      (generalMeanRows 172).J/2-(generalMeanRows 172).error (generalMeanGrid j.val)+
      (generalMeanRows 172).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 172).c)).2-
      (generalMeanRows 172).J/2-(generalMeanRows 172).error 4 := by
  have he : (generalMeanRows 172).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 172) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 172)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0172

/-! Kernel-checked entropy margins for general spectral rectangle 173. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0173
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5175444437, 4996069888, 4824973857, 4661671066, 4505710978, 4356674763, 4214172594, 4077841222, 3947341796, 3822357902, 3702593796, 3587772793, 3477635822, 3371940095, 3270457913, 3172975560, 3079292302, 2989219469, 2902579610, 2819205719, 2738940524, 2661635829, 2587151914, 2515356970, 2446126590, 2379343284, 2314896046, 2252679933, 2192595695, 2134549415, 2078452181, 2024219782, 1971772423, 1921034460, 1871934151, 1824403424, 1778377668, 1733795523, 1690598697, 1648731789, 1608142124, 1568779597, 1530596530, 1493547536, 1457589393, 1422680922, 1388782876, 1355857837, 1323870113, 1292785649, 1262571939, 1233197940, 1204633999, 1176851779, 1149824190, 1123525323, 1097930393, 1073015678, 1048758465, 1025137003, 1002130451, 979718830, 957882989, 936604556, 915865903, 895650109, 875940929, 856722757, 837980596, 819700034, 801867210, 784468794, 767491957, 750924351, 734754088, 718969715, 703560199, 688514904, 673823577, 659476327, 645463613, 631776226, 618405277, 605342180, 592578641, 580106648, 567918454, 556006569, 544363750, 532982990, 521857505, 510980732, 500346314, 489948095, 479780110, 469836579, 460111901, 450600643, 441297537, 432197473, 423295492, 414586783, 406066673, 397730626, 389574238, 381593228, 373783439, 366140828, 358661469, 351341541, 344177331, 337165226, 330301712, 323583369, 317006869, 310568974, 304266529, 298096463, 292055786, 286141584, 280351020]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 173).prefactor = (2518898509650879/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 173).cutoff/(generalMeanRows 173).c)).2 =
    (100934469306593/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 173).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 173).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 173).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 173

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 173).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 173).criticalRate j.val*(generalMeanRows 173).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 173).c*(generalMeanRows 173).criticalPoint j.val)).2-
      (generalMeanRows 173).J/2-(generalMeanRows 173).error (generalMeanGrid j.val)+
      (generalMeanRows 173).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 173).c)).2-
      (generalMeanRows 173).J/2-(generalMeanRows 173).error 4 := by
  have he : (generalMeanRows 173).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 173) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 173)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0173

/-! Kernel-checked entropy margins for general spectral rectangle 174. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0174
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5253353553, 5083288480, 4920942226, 4765859880, 4617619284, 4475828168, 4340121595, 4210159677, 4085625511, 3966223333, 3851676838, 3741727674, 3636134061, 3534669548, 3437121869, 3343291914, 3252992774, 3166048872, 3082295173, 3001576446, 2923746595, 2848668038, 2776211137, 2706253672, 2638680351, 2573382361, 2510256951, 2449207045, 2390140883, 2332971687, 2277617353, 2224000162, 2172046509, 2121686659, 2072854509, 2025487376, 1979525786, 1934913295, 1891596302, 1849523892, 1808647676, 1768921648, 1730302049, 1692747239, 1656217580, 1620675322, 1586084500, 1552410834, 1519621637, 1487685730, 1456573356, 1426256109, 1396706858, 1367899681, 1339809798, 1312413516, 1285688170, 1259612065, 1234164436, 1209325391, 1185075870, 1161397605, 1138273077, 1115685480, 1093618686, 1072057209, 1050986177, 1030391301, 1010258845, 990575601, 971328863, 952506405, 934096457, 916087682, 898469159, 881230362, 864361143, 847851714, 831692630, 815874775, 800389348, 785227846, 770382054, 755844033, 741606104, 727660841, 714001058, 700619800, 687510333, 674666134, 662080886, 649748462, 637662926, 625818520, 614209659, 602830923, 591677051, 580742936, 570023618, 559514278, 549210232, 539106931, 529199948, 519484981, 509957843, 500614462, 491450874, 482463220, 473647744, 465000786, 456518782, 448198261, 440035836, 432028211, 424172168, 416464571, 408902362, 401482557, 394202245, 387058584, 380048802]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 174).prefactor = (4773818086118309/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 174).cutoff/(generalMeanRows 174).c)).2 =
    (440386989387431/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 174).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 174).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 174).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 174

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 174).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 174).criticalRate j.val*(generalMeanRows 174).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 174).c*(generalMeanRows 174).criticalPoint j.val)).2-
      (generalMeanRows 174).J/2-(generalMeanRows 174).error (generalMeanGrid j.val)+
      (generalMeanRows 174).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 174).c)).2-
      (generalMeanRows 174).J/2-(generalMeanRows 174).error 4 := by
  have he : (generalMeanRows 174).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 174) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 174)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0174

/-! Kernel-checked entropy margins for general spectral rectangle 175. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0175
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5419273413, 5246661309, 5081860764, 4924410754, 4773883479, 4629881455, 4492034924, 4359999533, 4233454245, 4112099463, 3995655328, 3883860187, 3776469196, 3673253056, 3573996859, 3478499031, 3386570375, 3298033188, 3212720449, 3130475084, 3051149277, 2974603848, 2900707666, 2829337122, 2760375629, 2693713167, 2629245861, 2566875584, 2506509599, 2448060216, 2391444479, 2336583876, 2283404064, 2231834616, 2181808786, 2133263288, 2086138091, 2040376224, 1995923603, 1952728854, 1910743164, 1869920130, 1830215624, 1791587660, 1753996277, 1717403425, 1681772856, 1647070027, 1613262008, 1580317387, 1548206195, 1516899825, 1486370957, 1456593494, 1427542493, 1399194105, 1371525519, 1344514908, 1318141378, 1292384916, 1267226352, 1242647310, 1218630173, 1195158040, 1172214693, 1149784564, 1127852701, 1106404737, 1085426866, 1064905812, 1044828803, 1025183552, 1005958227, 987141435, 968722202, 950689946, 933034471, 915745937, 898814852, 882232054, 865988697, 850076234, 834486407, 819211233, 804242994, 789574222, 775197691, 761106408, 747293598, 733752701, 720477359, 707461410, 694698880, 682183972, 669911065, 657874700, 646069581, 634490562, 623132647, 611990979, 601060838, 590337637, 579816913, 569494325, 559365650, 549426778, 539673708, 530102543, 520709489, 511490848, 502443019, 493562492, 484845842, 476289734, 467890913, 459646203, 451552508, 443606805, 435806143, 428147643, 420628492]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 175).prefactor = (4837303421853809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 175).cutoff/(generalMeanRows 175).c)).2 =
    (44855030002659/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 175).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 175).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 175).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 175

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 175).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 175).criticalRate j.val*(generalMeanRows 175).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 175).c*(generalMeanRows 175).criticalPoint j.val)).2-
      (generalMeanRows 175).J/2-(generalMeanRows 175).error (generalMeanGrid j.val)+
      (generalMeanRows 175).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 175).c)).2-
      (generalMeanRows 175).J/2-(generalMeanRows 175).error 4 := by
  have he : (generalMeanRows 175).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 175) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 175)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0175

/-! Kernel-checked entropy margins for general spectral rectangle 176. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0176
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4868479578, 4692222480, 4524228193, 4364010810, 4211119232, 4065134132, 3925665247, 3792348944, 3664846037, 3542839826, 3426034316, 3314152610, 3206935458, 3104139923, 3005538178, 2910916409, 2820073798, 2732821613, 2648982355, 2568388983, 2490884204, 2416319810, 2344556076, 2275461199, 2208910782, 2144787352, 2082979922, 2023383576, 1965899089, 1910432576, 1856895155, 1805202651, 1755275302, 1707037501, 1660417540, 1615347388, 1571762467, 1529601458, 1488806105, 1449321044, 1411093639, 1374073822, 1338213953, 1303468684, 1269794830, 1237151249, 1205498735, 1174799906, 1145019112, 1116122336, 1088077110, 1060852435, 1034418697, 1008747602, 983812103, 959586335, 936045557, 913166094, 890925280, 869301411, 848273696, 827822208, 807927848, 788572296, 769737982, 751408041, 733566285, 716197168, 699285757, 682817702, 666779207, 651157008, 635938346, 621110943, 606662982, 592583085, 578860293, 565484049, 552444177, 539730868, 527334663, 515246437, 503457387, 491959015, 480743115, 469801766, 459127313, 448712361, 438549761, 428632601, 418954200, 409508090, 400288018, 391287928, 382501960, 373924439, 365549869, 357372924, 349388445, 341591431, 333977035, 326540554, 319277430, 312183240, 305253693, 298484623, 291871988, 285411864, 279100439, 272934011, 266908985, 261021866, 255269260, 249647867, 244154478, 238785975, 233539325, 228411579, 223399865, 218501394, 213713449]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 176).prefactor = (5033216527289729/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 176).cutoff/(generalMeanRows 176).c)).2 =
    (386024326620739/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 176).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 176).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 176).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 176

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 176).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 176).criticalRate j.val*(generalMeanRows 176).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 176).c*(generalMeanRows 176).criticalPoint j.val)).2-
      (generalMeanRows 176).J/2-(generalMeanRows 176).error (generalMeanGrid j.val)+
      (generalMeanRows 176).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 176).c)).2-
      (generalMeanRows 176).J/2-(generalMeanRows 176).error 4 := by
  have he : (generalMeanRows 176).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 176) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 176)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0176

/-! Kernel-checked entropy margins for general spectral rectangle 177. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0177
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4817045131, 4640216643, 4471712056, 4311042060, 4157752366, 4011420659, 3871653863, 3738085701, 3610374496, 3488201197, 3371267593, 3259294691, 3152021257, 3049202477, 2950608749, 2856024568, 2765247521, 2678087353, 2594365123, 2513912417, 2436570637, 2362190333, 2290630597, 2221758499, 2155448567, 2091582308, 2030047755, 1970739063, 1913556118, 1858404186, 1805193576, 1753839340, 1704260977, 1656382175, 1610130552, 1565437432, 1522237623, 1480469217, 1440073396, 1400994260, 1363178658, 1326576033, 1291138274, 1256819586, 1223576354, 1191367029, 1160152012, 1129893548, 1100555630, 1072103900, 1044505565, 1017729313, 991745237, 966524757, 942040556, 918266513, 895177640, 872750028, 850960789, 829788006, 809210685, 789208709, 769762793, 750854445, 732465929, 714580223, 697180991, 680252546, 663779820, 647748337, 632144182, 616953977, 602164856, 587764442, 573740820, 560082526, 546778515, 533818152, 521191188, 508887744, 496898297, 485213663, 473824982, 462723705, 451901579, 441350637, 431063187, 421031794, 411249276, 401708694, 392403335, 383326710, 374472542, 365834759, 357407482, 349185024, 341161876, 333332704, 325692342, 318235784, 310958178, 303854823, 296921161, 290152770, 283545363, 277094782, 270796991, 264648074, 258644229, 252781767, 247057103, 241466758, 236007351, 230675599, 225468310, 220382383, 215414804, 210562643, 205823051, 201193257, 196670566]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 177).prefactor = (1013418464645517/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 177).cutoff/(generalMeanRows 177).c)).2 =
    (378181149159711/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 177).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 177).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 177).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 177

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 177).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 177).criticalRate j.val*(generalMeanRows 177).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 177).c*(generalMeanRows 177).criticalPoint j.val)).2-
      (generalMeanRows 177).J/2-(generalMeanRows 177).error (generalMeanGrid j.val)+
      (generalMeanRows 177).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 177).c)).2-
      (generalMeanRows 177).J/2-(generalMeanRows 177).error 4 := by
  have he : (generalMeanRows 177).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 177) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 177)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0177

/-! Kernel-checked entropy margins for general spectral rectangle 178. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0178
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4890065040, 4713072779, 4544361266, 4383444767, 4229872288, 4083224547, 3943111264, 3809168740, 3681057681, 3558461232, 3441083211, 3328646504, 3220891611, 3117575326, 3018469532, 2923360101, 2832045895, 2744337844, 2660058101, 2579039271, 2501123700, 2426162814, 2354016520, 2284552646, 2217646423, 2153180010, 2091042052, 2031127267, 1973336071, 1917574219, 1863752478, 1811786326, 1761595660, 1713104536, 1666240920, 1620936455, 1577126252, 1534748680, 1493745186, 1454060112, 1415640534, 1378436107, 1342398922, 1307483365, 1273645996, 1240845427, 1209042207, 1178198724, 1148279099, 1119249097, 1091076038, 1063728716, 1037177321, 1011393364, 986349613, 962020025, 938379685, 915404749, 893072393, 871360756, 850248896, 829716744, 809745058, 790315388, 771410031, 753011999, 735104985, 717673327, 700701982, 684176491, 668082958, 652408020, 637138821, 622262995, 607768635, 593644280, 579878891, 566461832, 553382854, 540632075, 528199969, 516077344, 504255334, 492725381, 481479221, 470508876, 459806639, 449365063, 439176949, 429235341, 419533508, 410064944, 400823350, 391802634, 382996895, 374400424, 366007687, 357813328, 349812154, 341999134, 334369390, 326918193, 319640957, 312533233, 305590705, 298809185, 292184608, 285713027, 279390610, 273213635, 267178488, 261281657, 255519730, 249889389, 244387410, 239010661, 233756093, 228620742, 223601726, 218696240, 213901555]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 178).prefactor = (5035518212246931/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 178).cutoff/(generalMeanRows 178).c)).2 =
    (47865443617811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 178).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 178).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 178).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 178

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 178).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 178).criticalRate j.val*(generalMeanRows 178).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 178).c*(generalMeanRows 178).criticalPoint j.val)).2-
      (generalMeanRows 178).J/2-(generalMeanRows 178).error (generalMeanGrid j.val)+
      (generalMeanRows 178).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 178).c)).2-
      (generalMeanRows 178).J/2-(generalMeanRows 178).error 4 := by
  have he : (generalMeanRows 178).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 178) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 178)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0178

/-! Kernel-checked entropy margins for general spectral rectangle 179. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0179
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4822576542, 4645600686, 4476939050, 4316104119, 4162643217, 4016135470, 3876189090, 3742438947, 3614544389, 3492187268, 3375070175, 3262914823, 3155460596, 3052463223, 2953693569, 2858936536, 2767990057, 2680664172, 2596780186, 2516169889, 2438674848, 2364145742, 2292441764, 2223430054, 2156985187, 2092988692, 2031328607, 1971899073, 1914599948, 1859336453, 1806018845, 1754562108, 1704885670, 1656913133, 1610572031, 1565793591, 1522512523, 1480666817, 1440197550, 1401048714, 1363167049, 1326501886, 1291005006, 1256630500, 1223334645, 1191075780, 1159814196, 1129512033, 1100133173, 1071643156, 1044009085, 1017199546, 991184533, 965935369, 941424643, 917626139, 894514782, 872066573, 850258540, 829068684, 808475929, 788460081, 769001780, 750082463, 731684321, 713790266, 696383896, 679449461, 662971832, 646936475, 631329418, 616137230, 601346992, 586946277, 572923124, 559266021, 545963881, 533006025, 520382164, 508082382, 496097117, 484417152, 473033591, 461937854, 451121658, 440577006, 430296178, 420271713, 410496405, 400963288, 391665628, 382596915, 373750851, 365121343, 356702496, 348488603, 340474140, 332653757, 325022273, 317574668, 310306077, 303211787, 296287226, 289527964, 282929702, 276488272, 270199629, 264059849, 258065122, 252211750, 246496142, 240914813, 235464375, 230141540, 224943109, 219865979, 214907130, 210063626, 205332617, 200711327, 196197059]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 179).prefactor = (1263142133766983/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 179).cutoff/(generalMeanRows 179).c)).2 =
    (375080371481463/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 179).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 179).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 179).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 179

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 179).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 179).criticalRate j.val*(generalMeanRows 179).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 179).c*(generalMeanRows 179).criticalPoint j.val)).2-
      (generalMeanRows 179).J/2-(generalMeanRows 179).error (generalMeanGrid j.val)+
      (generalMeanRows 179).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 179).c)).2-
      (generalMeanRows 179).J/2-(generalMeanRows 179).error 4 := by
  have he : (generalMeanRows 179).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 179) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 179)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0179

/-! Kernel-checked entropy margins for general spectral rectangle 180. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0180
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4762097622, 4585033589, 4416306395, 4255428534, 4101947259, 3955441544, 3815519383, 3681815370, 3553988517, 3431720300, 3314712888, 3202687537, 3095383146, 2992554929, 2893973216, 2799422355, 2708699710, 2621614740, 2537988162, 2457651172, 2380444734, 2306218930, 2234832350, 2166151536, 2100050467, 2036410082, 1975117837, 1916067294, 1859157741, 1804293841, 1751385301, 1700346566, 1651096533, 1603558288, 1557658860, 1513328982, 1470502884, 1429118086, 1389115210, 1350437806, 1313032182, 1276847254, 1241834397, 1207947312, 1175141896, 1143376122, 1112609928, 1082805111, 1053925227, 1025935495, 998802715, 972495180, 946982599, 922236026, 898227788, 874931422, 852321610, 830374128, 809065782, 788374365, 768278602, 748758107, 729793339, 711365561, 693456800, 676049813, 659128047, 642675614, 626677251, 611118297, 595984662, 581262803, 566939696, 553002813, 539440102, 526239963, 513391226, 500883139, 488705341, 476847850, 465301045, 454055651, 443102723, 432433632, 422040055, 411913956, 402047578, 392433432, 383064283, 373933142, 365033255, 356358093, 347901345, 339656907, 331618874, 323781535, 316139362, 308687004, 301419280, 294331176, 287417831, 280674540, 274096741, 267680015, 261420078, 255312775, 249354077, 243540079, 237866990, 232331132, 226928938, 221656943, 216511786, 211490201, 206589019, 201805161, 197135635, 192577537, 188128043, 183784409, 179543969]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 180).prefactor = (631873737304251/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 180).cutoff/(generalMeanRows 180).c)).2 =
    (182103519234867/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 180).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 180).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 180).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 180

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 180).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 180).criticalRate j.val*(generalMeanRows 180).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 180).c*(generalMeanRows 180).criticalPoint j.val)).2-
      (generalMeanRows 180).J/2-(generalMeanRows 180).error (generalMeanGrid j.val)+
      (generalMeanRows 180).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 180).c)).2-
      (generalMeanRows 180).J/2-(generalMeanRows 180).error 4 := by
  have he : (generalMeanRows 180).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 180) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 180)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0180

/-! Kernel-checked entropy margins for general spectral rectangle 181. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0181
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5303390712, 5134651650, 4973606228, 4819795656, 4672794428, 4532207414, 4397667257, 4268832044, 4145383209, 4027023647, 3913476008, 3804481155, 3699796761, 3599196036, 3502466572, 3409409279, 3319837420, 3233575728, 3150459590, 3070334305, 2993054394, 2918482974, 2846491176, 2776957602, 2709767838, 2644813986, 2581994249, 2521212531, 2462378072, 2405405116, 2350212588, 2296723807, 2244866213, 2194571112, 2145773443, 2098411555, 2052427002, 2007764355, 1964371019, 1922197068, 1881195089, 1841320035, 1802529086, 1764781528, 1728038626, 1692263512, 1657421086, 1623477911, 1590402122, 1558163340, 1526732588, 1496082219, 1466185837, 1437018236, 1408555332, 1380774105, 1353652540, 1327169579, 1301305065, 1276039699, 1251354996, 1227233240, 1203657446, 1180611325, 1158079245, 1136046204, 1114497791, 1093420162, 1072800013, 1052624549, 1032881464, 1013558912, 994645493, 976130223, 958002523, 940252192, 922869396, 905844648, 889168790, 872832983, 856828691, 841147665, 825781934, 810723788, 795965772, 781500672, 767321506, 753421511, 739794138, 726433042, 713332071, 700485261, 687886827, 675531157, 663412802, 651526475, 639867039, 628429505, 617209023, 606200882, 595400498, 584803416, 574405299, 564201928, 554189199, 544363111, 534719772, 525255389, 515966266, 506848804, 497899491, 489114905, 480491708, 472026645, 463716539, 455558292, 447548877, 439685343, 431964807, 424384451, 416941527]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 181).prefactor = (599808990308333/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 181).cutoff/(generalMeanRows 181).c)).2 =
    (115205098154601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 181).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 181).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 181).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 181

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 181).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 181).criticalRate j.val*(generalMeanRows 181).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 181).c*(generalMeanRows 181).criticalPoint j.val)).2-
      (generalMeanRows 181).J/2-(generalMeanRows 181).error (generalMeanGrid j.val)+
      (generalMeanRows 181).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 181).c)).2-
      (generalMeanRows 181).J/2-(generalMeanRows 181).error 4 := by
  have he : (generalMeanRows 181).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 181) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 181)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0181

/-! Kernel-checked entropy margins for general spectral rectangle 182. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0182
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5337464447, 5167641253, 5005561132, 4850762343, 4702816647, 4561326376, 4425921812, 4296258846, 4172016865, 4052896856, 3938619685, 3828924552, 3723567571, 3622320497, 3524969556, 3431314379, 3341167031, 3254351117, 3170700966, 3090060884, 3012284457, 2937233925, 2864779586, 2794799267, 2727177815, 2661806641, 2598583294, 2537411059, 2478198596, 2420859594, 2365312459, 2311480019, 2259289245, 2208671004, 2159559815, 2111893631, 2065613632, 2020664032, 1976991899, 1934546985, 1893281572, 1853150325, 1814110149, 1776120066, 1739141094, 1703136130, 1668069845, 1633908588, 1600620291, 1568174377, 1536541686, 1505694392, 1475605929, 1446250929, 1417605154, 1389645435, 1362349617, 1335696505, 1309665815, 1284238122, 1259394822, 1235118086, 1211390820, 1188196630, 1165519784, 1143345183, 1121658323, 1100445273, 1079692642, 1059387553, 1039517620, 1020070923, 1001035987, 982401759, 964157590, 946293215, 928798737, 911664605, 894881607, 878440844, 862333727, 846551952, 831087497, 815932604, 801079769, 786521733, 772251467, 758262166, 744547239, 731100299, 717915155, 704985806, 692306429, 679871374, 667675161, 655712465, 643978119, 632467099, 621174527, 610095659, 599225884, 588560717, 578095793, 567826867, 557749807, 547860587, 538155291, 528630100, 519281296, 510105255, 501098443, 492257417, 483578817, 475059367, 466695870, 458485206, 450424332, 442510276, 434740136, 427111077, 419620333]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 182).prefactor = (1207325401585319/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 182).cutoff/(generalMeanRows 182).c)).2 =
    (115205098154601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 182).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 182).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 182).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 182

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 182).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 182).criticalRate j.val*(generalMeanRows 182).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 182).c*(generalMeanRows 182).criticalPoint j.val)).2-
      (generalMeanRows 182).J/2-(generalMeanRows 182).error (generalMeanGrid j.val)+
      (generalMeanRows 182).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 182).c)).2-
      (generalMeanRows 182).J/2-(generalMeanRows 182).error 4 := by
  have he : (generalMeanRows 182).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 182) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 182)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0182

/-! Kernel-checked entropy margins for general spectral rectangle 183. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0183
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4766641940, 4589273093, 4420289029, 4259196986, 4105539446, 3958891060, 3818855906, 3685065028, 3557174227, 3434862075, 3317828115, 3205791236, 3098488200, 2995672298, 2897112129, 2802590490, 2711903351, 2624858928, 2541276824, 2460987245, 2383830278, 2309655225, 2238319990, 2169690513, 2103640243, 2040049662, 1978805826, 1919801957, 1862937055, 1808115537, 1755246906, 1704245443, 1655029912, 1607523298, 1561652552, 1517348357, 1474544913, 1433179727, 1393193429, 1354529586, 1317134541, 1280957254, 1245949153, 1212064002, 1179257767, 1147488498, 1116716213, 1086902793, 1058011881, 1030008790, 1002860410, 976535127, 951002747, 926234418, 902202561, 878880808, 856243935, 834267809, 812929329, 792206376, 772077762, 752523188, 733523198, 715059134, 697113105, 679667943, 662707171, 646214971, 630176153, 614576122, 599400852, 584636864, 570271192, 556291368, 542685394, 529441721, 516549233, 503997223, 491775378, 479873758, 468282786, 456993224, 445996166, 435283018, 424845490, 414675579, 404765556, 395107962, 385695587, 376521468, 367578873, 358861296, 350362446, 342076237, 333996783, 326118388, 318435538, 310942898, 303635300, 296507738, 289555366, 282773486, 276157545, 269703132, 263405968, 257261906, 251266924, 245417117, 239708701, 234138001, 228701451, 223395589, 218217055, 213162584, 208229006, 203413244, 198712305, 194123282, 189643352, 185269768, 180999861]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 183).prefactor = (5101196118406933/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 183).cutoff/(generalMeanRows 183).c)).2 =
    (46299876089707/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 183).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 183).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 183).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 183

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 183).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 183).criticalRate j.val*(generalMeanRows 183).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 183).c*(generalMeanRows 183).criticalPoint j.val)).2-
      (generalMeanRows 183).J/2-(generalMeanRows 183).error (generalMeanGrid j.val)+
      (generalMeanRows 183).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 183).c)).2-
      (generalMeanRows 183).J/2-(generalMeanRows 183).error 4 := by
  have he : (generalMeanRows 183).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 183) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 183)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0183

/-! Kernel-checked entropy margins for general spectral rectangle 184. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0184
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4798723570, 4620160952, 4450039549, 4287863284, 4133171560, 3985536166, 3844558513, 3709867162, 3581115599, 3457980231, 3340158580, 3227367643, 3119342410, 3015834511, 2916610988, 2821453176, 2730155672, 2642525401, 2558380752, 2477550788, 2399874521, 2325200237, 2253384884, 2184293499, 2117798682, 2053780107, 1992124073, 1932723082, 1875475453, 1820284962, 1767060502, 1715715776, 1666169003, 1618342648, 1572163171, 1527560790, 1484469259, 1442825667, 1402570243, 1363646175, 1325999445, 1289578668, 1254334948, 1220221734, 1187194699, 1155211608, 1124232212, 1094218134, 1065132774, 1036941209, 1009610108, 983107645, 957403421, 932468389, 908274788, 884796068, 862006840, 839882804, 818400707, 797538278, 777274190, 757588006, 738460137, 719871802, 701804988, 684242412, 667167486, 650564287, 634417520, 618712493, 603435088, 588571731, 574109372, 560035458, 546337909, 533005100, 520025840, 507389350, 495085246, 483103523, 471434538, 460068993, 448997919, 438212668, 427704890, 417466530, 407489809, 397767215, 388291491, 379055625, 370052843, 361276593, 352720542, 344378563, 336244731, 328313310, 320578752, 313035683, 305678901, 298503368, 291504203, 284676677, 278016208, 271518354, 265178808, 258993394, 252958062, 247068884, 241322048, 235713854, 230240714, 224899141, 219685753, 214597263, 209630481, 204782306, 200049727, 195429819, 190919737, 186516716, 182218071]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 184).prefactor = (1027105889472901/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 184).cutoff/(generalMeanRows 184).c)).2 =
    (46299876089707/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 184).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 184).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 184).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 184

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 184).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 184).criticalRate j.val*(generalMeanRows 184).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 184).c*(generalMeanRows 184).criticalPoint j.val)).2-
      (generalMeanRows 184).J/2-(generalMeanRows 184).error (generalMeanGrid j.val)+
      (generalMeanRows 184).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 184).c)).2-
      (generalMeanRows 184).J/2-(generalMeanRows 184).error 4 := by
  have he : (generalMeanRows 184).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 184) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 184)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0184

/-! Kernel-checked entropy margins for general spectral rectangle 185. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0185
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5275569666, 5104932132, 4942097500, 4786601141, 4638012108, 4495930185, 4359983258, 4229824960, 4105132544, 3985604981, 3870961231, 3760938681, 3655291733, 3553790509, 3456219687, 3362377420, 3272074367, 3185132793, 3101385749, 3020676315, 2942856912, 2867788657, 2795340784, 2725390089, 2657820440, 2592522305, 2529392326, 2468332922, 2409251916, 2352062199, 2296681405, 2243031618, 2191039099, 2140634026, 2091750258, 2044325110, 1998299149, 1953615997, 1910222152, 1868066816, 1827101741, 1787281080, 1748561245, 1710900782, 1674260248, 1638602095, 1603890569, 1570091604, 1537172731, 1505102989, 1473852844, 1443394110, 1413699874, 1384744433, 1356503223, 1328952762, 1302070593, 1275835228, 1250226100, 1225223512, 1200808597, 1176963269, 1153670190, 1130912728, 1108674922, 1086941450, 1065697597, 1044929224, 1024622740, 1004765076, 985343662, 966346397, 947761635, 929578156, 911785149, 894372196, 877329249, 860646616, 844314942, 828325198, 812668665, 797336915, 782321808, 767615471, 753210290, 739098899, 725274167, 711729193, 698457290, 685451983, 672706994, 660216237, 647973810, 635973990, 624211220, 612680107, 601375417, 590292063, 579425105, 568769742, 558321306, 548075260, 538027189, 528172801, 518507916, 509028469, 499730499, 490610151, 481663669, 472887396, 464277765, 455831301, 447544617, 439414410, 431437458, 423610617, 415930823, 408395082, 401000475, 393744150, 386623325]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 185).prefactor = (4860329367733727/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 185).cutoff/(generalMeanRows 185).c)).2 =
    (113164270494811/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 185).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 185).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 185).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 185

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 185).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 185).criticalRate j.val*(generalMeanRows 185).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 185).c*(generalMeanRows 185).criticalPoint j.val)).2-
      (generalMeanRows 185).J/2-(generalMeanRows 185).error (generalMeanGrid j.val)+
      (generalMeanRows 185).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 185).c)).2-
      (generalMeanRows 185).J/2-(generalMeanRows 185).error 4 := by
  have he : (generalMeanRows 185).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 185) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 185)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0185

/-! Kernel-checked entropy margins for general spectral rectangle 186. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0186
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5214876416, 5043464887, 4879916141, 4723762612, 4574570591, 4431937269, 4295488094, 4164874396, 4039771258, 3919875597, 3804904430, 3694593305, 3588694875, 3486977605, 3389224595, 3295232499, 3204810547, 3117779640, 3033971530, 2953228056, 2875400452, 2800348704, 2727940957, 2658052972, 2590567619, 2525374414, 2462369084, 2401453169, 2342533651, 2285522610, 2230336904, 2176897870, 2125131049, 2074965929, 2026335704, 1979177051, 1933429918, 1889037336, 1845945230, 1804102254, 1763459629, 1723970996, 1685592275, 1648281538, 1611998883, 1576706322, 1542367674, 1508948462, 1476415822, 1444738412, 1413886328, 1383831028, 1354545259, 1326002983, 1298179320, 1271050480, 1244593707, 1218787228, 1193610198, 1169042656, 1145065475, 1121660323, 1098809623, 1076496511, 1054704805, 1033418968, 1012624078, 992305798, 972450344, 953044464, 934075408, 915530906, 897399144, 879668745, 862328746, 845368580, 828778058, 812547351, 796666977, 781127778, 765920915, 751037845, 736470316, 722210348, 708250225, 694582483, 681199898, 668095477, 655262448, 642694253, 630384535, 618327133, 606516074, 594945565, 583609984, 572503876, 561621947, 550959054, 540510203, 530270542, 520235356, 510400061, 500760200, 491311438, 482049559, 472970460, 464070146, 455344732, 446790431, 438403556, 430180517, 422117814, 414212037, 406459861, 398858048, 391403436, 384092943, 376923564, 369892364, 362996483, 356233126]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 186).prefactor = (4891556479271503/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 186).cutoff/(generalMeanRows 186).c)).2 =
    (3556478973973/8000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 186).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 186).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 186).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 186

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 186).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 186).criticalRate j.val*(generalMeanRows 186).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 186).c*(generalMeanRows 186).criticalPoint j.val)).2-
      (generalMeanRows 186).J/2-(generalMeanRows 186).error (generalMeanGrid j.val)+
      (generalMeanRows 186).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 186).c)).2-
      (generalMeanRows 186).J/2-(generalMeanRows 186).error 4 := by
  have he : (generalMeanRows 186).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 186) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 186)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0186

/-! Kernel-checked entropy margins for general spectral rectangle 187. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0187
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5188746761, 5018128278, 4855307283, 4699822468, 4551245817, 4409179698, 4273254263, 4143125118, 4018471232, 3898993053, 3784410803, 3674462938, 3568904752, 3467507104, 3370055258, 3276347833, 3186195832, 3099421763, 3015858823, 2935350158, 2857748178, 2782913926, 2710716497, 2641032502, 2573745574, 2508745907, 2445929837, 2385199442, 2326462181, 2269630557, 2214621798, 2161357568, 2109763694, 2059769911, 2011309627, 1964319700, 1918740239, 1874514403, 1831588228, 1789910458, 1749432386, 1710107710, 1671892393, 1634744538, 1598624262, 1563493588, 1529316336, 1496058025, 1463685777, 1432168235, 1401475472, 1371578923, 1342451303, 1314066547, 1286399738, 1259427052, 1233125699, 1207473868, 1182450677, 1158036127, 1134211055, 1110957091, 1088256622, 1066092749, 1044449255, 1023310569, 1002661737, 982488389, 962776713, 943513427, 924685754, 906281397, 888288519, 870695720, 853492013, 836666814, 820209913, 804111466, 788361973, 772952264, 757873484, 743117082, 728674793, 714538629, 700700867, 687154036, 673890907, 660904483, 648187989, 635734865, 623538754, 611593494, 599893114, 588431821, 577203999, 566204196, 555427120, 544867637, 534520757, 524381634, 514445562, 504707964, 495164391, 485810519, 476642139, 467655160, 458845597, 450209575, 441743319, 433443155, 425305503, 417326875, 409503875, 401833192, 394311597, 386935944, 379703165, 372610266, 365654329, 358832505, 352142015]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 187).prefactor = (4833349302062013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 187).cutoff/(generalMeanRows 187).c)).2 =
    (54800750771531/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 187).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 187).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 187).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 187

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 187).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 187).criticalRate j.val*(generalMeanRows 187).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 187).c*(generalMeanRows 187).criticalPoint j.val)).2-
      (generalMeanRows 187).J/2-(generalMeanRows 187).error (generalMeanGrid j.val)+
      (generalMeanRows 187).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 187).c)).2-
      (generalMeanRows 187).J/2-(generalMeanRows 187).error 4 := by
  have he : (generalMeanRows 187).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 187) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 187)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0187

/-! Kernel-checked entropy margins for general spectral rectangle 188. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0188
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5130520289, 4959155501, 4795648281, 4639534314, 4490382765, 4347793349, 4211393725, 4080837146, 3955800365, 3835981732, 3721099485, 3610890203, 3505107395, 3403520229, 3305912364, 3212080887, 3121835347, 3034996865, 2951397316, 2870878584, 2793291874, 2718497077, 2646362188, 2576762765, 2509581432, 2444707419, 2382036135, 2321468771, 2262911936, 2206277316, 2151481356, 2098444968, 2047093254, 1997355257, 1949163716, 1902454849, 1857168145, 1813246172, 1770634395, 1729281006, 1689136772, 1650154879, 1612290803, 1575502172, 1539748651, 1504991824, 1471195090, 1438323562, 1406343971, 1375224581, 1344935106, 1315446628, 1286731527, 1258763412, 1231517056, 1204968331, 1179094159, 1153872448, 1129282048, 1105302700, 1081914993, 1059100316, 1036840825, 1015119397, 993919602, 973225663, 953022427, 933295334, 914030388, 895214131, 876833616, 858876383, 841330439, 824184232, 807426633, 791046917, 775034744, 759380140, 744073483, 729105486, 714467183, 700149913, 686145310, 672445288, 659042028, 645927970, 633095798, 620538434, 608249026, 596220937, 584447740, 572923206, 561641299, 550596166, 539782132, 529193690, 518825498, 508672370, 498729272, 488991314, 479453747, 470111956, 460961457, 451997890, 443217017, 434614714, 426186972, 417929887, 409839663, 401912602, 394145106, 386533669, 379074878, 371765406, 364602012, 357581540, 350700909, 343957118, 337347240, 330868422, 324517878]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 188).prefactor = (2432443157396041/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 188).cutoff/(generalMeanRows 188).c)).2 =
    (430373834474981/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 188).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 188).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 188).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 188

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 188).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 188).criticalRate j.val*(generalMeanRows 188).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 188).c*(generalMeanRows 188).criticalPoint j.val)).2-
      (generalMeanRows 188).J/2-(generalMeanRows 188).error (generalMeanGrid j.val)+
      (generalMeanRows 188).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 188).c)).2-
      (generalMeanRows 188).J/2-(generalMeanRows 188).error 4 := by
  have he : (generalMeanRows 188).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 188) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 188)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0188

/-! Kernel-checked entropy margins for general spectral rectangle 189. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0189
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5209004653, 5037695233, 4874200210, 4718058456, 4568842067, 4426153459, 4289622775, 4158905565, 4033680696, 3913648474, 3798528944, 3688060355, 3581997766, 3480111776, 3382187374, 3288022881, 3197428992, 3110227891, 3026252446, 2945345462, 2867359004, 2792153766, 2719598490, 2649569435, 2581949879, 2516629665, 2453504776, 2392476943, 2333453281, 2276345950, 2221071844, 2167552297, 2115712810, 2065482798, 2016795356, 1969587039, 1923797653, 1879370066, 1836250030, 1794386009, 1753729025, 1714232513, 1675852179, 1638545877, 1602273483, 1566996783, 1532679372, 1499286545, 1466785215, 1435143813, 1404332215, 1374321661, 1345084679, 1316595023, 1288827603, 1261758425, 1235364535, 1209623967, 1184515687, 1160019550, 1136116253, 1112787290, 1090014917, 1067782110, 1046072531, 1024870494, 1004160930, 983929364, 964161880, 944845097, 925966140, 907512623, 889472620, 871834644, 854587630, 837720914, 821224212, 805087607, 789301530, 773856745, 758744334, 743955684, 729482473, 715316656, 701450456, 687876351, 674587062, 661575546, 648834981, 636358765, 624140498, 612173980, 600453200, 588972330, 577725718, 566707878, 555913488, 545337380, 534974537, 524820086, 514869290, 505117549, 495560390, 486193463, 477012539, 468013503, 459192351, 450545188, 442068219, 433757752, 425610190, 417622029, 409789857, 402110347, 394580257, 387196425, 379955771, 372855289, 365892048, 359063187, 352365916]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 189).prefactor = (2417668974589091/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 189).cutoff/(generalMeanRows 189).c)).2 =
    (4353432166417/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 189).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 189).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 189).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 189

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 189).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 189).criticalRate j.val*(generalMeanRows 189).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 189).c*(generalMeanRows 189).criticalPoint j.val)).2-
      (generalMeanRows 189).J/2-(generalMeanRows 189).error (generalMeanGrid j.val)+
      (generalMeanRows 189).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 189).c)).2-
      (generalMeanRows 189).J/2-(generalMeanRows 189).error 4 := by
  have he : (generalMeanRows 189).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 189) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 189)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0189

/-! Kernel-checked entropy margins for general spectral rectangle 190. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0190
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5134199136, 4962695767, 4799041595, 4642773976, 4493463569, 4350711427, 4214146395, 4083422786, 3958218288, 3838232080, 3723183130, 3612808653, 3506862720, 3405114979, 3307349509, 3213363753, 3122967564, 3035982315, 2952240090, 2871582944, 2793862214, 2718937893, 2646678049, 2576958285, 2509661251, 2444676180, 2381898466, 2321229271, 2262575160, 2205847761, 2150963454, 2097843075, 2046411641, 1996598104, 1948335108, 1901558770, 1856208474, 1812226682, 1769558746, 1728152751, 1687959348, 1648931613, 1611024907, 1574196746, 1538406682, 1503616190, 1469788558, 1436888790, 1404883512, 1373740884, 1343430516, 1313923389, 1285191787, 1257209221, 1229950371, 1203391021, 1177508001, 1152279135, 1127683191, 1103699827, 1080309555, 1057493690, 1035234312, 1013514231, 992316947, 971626619, 951428029, 931706558, 912448152, 893639295, 875266987, 857318718, 839782443, 822646564, 805899907, 789531703, 773531569, 757889493, 742595814, 727641210, 713016678, 698713526, 684723357, 671038052, 657649767, 644550913, 631734149, 619192372, 606918706, 594906494, 583149287, 571640836, 560375087, 549346170, 538548391, 527976229, 517624326, 507487484, 497560653, 487838933, 478317562, 468991916, 459857499, 450909942, 442144997, 433558533, 425146533, 416905086, 408830389, 400918738, 393166528, 385570250, 378126485, 370831901, 363683255, 356677384, 349811206, 343081717, 336485987, 330021160, 323684449]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 190).prefactor = (4851210008735177/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 190).cutoff/(generalMeanRows 190).c)).2 =
    (85462208988887/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 190).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 190).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 190).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 190

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 190).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 190).criticalRate j.val*(generalMeanRows 190).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 190).c*(generalMeanRows 190).criticalPoint j.val)).2-
      (generalMeanRows 190).J/2-(generalMeanRows 190).error (generalMeanGrid j.val)+
      (generalMeanRows 190).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 190).c)).2-
      (generalMeanRows 190).J/2-(generalMeanRows 190).error 4 := by
  have he : (generalMeanRows 190).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 190) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 190)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0190

/-! Kernel-checked entropy margins for general spectral rectangle 191. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0191
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5064697850, 4892911956, 4729000743, 4572501710, 4422985566, 4280053325, 4143333717, 4012480870, 3887172227, 3767106664, 3652002799, 3541597454, 3435644269, 3333912430, 3236185523, 3142260476, 3051946606, 2965064732, 2881446372, 2800933003, 2723375377, 2648632893, 2576573023, 2507070774, 2440008197, 2375273926, 2312762764, 2252375280, 2194017456, 2137600341, 2083039743, 2030255932, 1979173372, 1929720468, 1881829327, 1835435539, 1790477973, 1746898583, 1704642229, 1663656512, 1623891611, 1585300142, 1547837016, 1511459313, 1476126160, 1441798616, 1408439568, 1376013630, 1344487047, 1313827611, 1284004575, 1254988575, 1226751559, 1199266715, 1172508408, 1146452119, 1121074384, 1096352746, 1072265697, 1048792635, 1025913814, 1003610305, 981863952, 960657338, 939973745, 919797119, 900112042, 880903701, 862157853, 843860805, 825999385, 808560918, 791533202, 774904488, 758663457, 742799202, 727301209, 712159339, 697363812, 682905191, 668774365, 654962538, 641461213, 628262181, 615357505, 602739513, 590400787, 578334146, 566532645, 554989558, 543698373, 532652785, 521846681, 511274139, 500929419, 490806952, 480901341, 471207346, 461719882, 452434016, 443344956, 434448049, 425738774, 417212740, 408865678, 400693440, 392691992, 384857409, 377185876, 369673681, 362317210, 355112947, 348057469, 341147442, 334379621, 327750844, 321258031, 314898180, 308668367, 302565741, 296587522]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 191).prefactor = (194132249472509/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 191).cutoff/(generalMeanRows 191).c)).2 =
    (416289437808371/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 191).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 191).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 191).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 191

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 191).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 191).criticalRate j.val*(generalMeanRows 191).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 191).c*(generalMeanRows 191).criticalPoint j.val)).2-
      (generalMeanRows 191).J/2-(generalMeanRows 191).error (generalMeanGrid j.val)+
      (generalMeanRows 191).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 191).c)).2-
      (generalMeanRows 191).J/2-(generalMeanRows 191).error 4 := by
  have he : (generalMeanRows 191).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 191) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 191)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0191

/-! Kernel-checked entropy margins for general spectral rectangle 192. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0192
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5081452933, 4909098736, 4744645270, 4587628505, 4437617731, 4294212639, 4157040734, 4025754999, 3900031809, 3779569044, 3664084390, 3553313802, 3447010101, 3344941712, 3246891504, 3152655733, 3062043086, 2974873788, 2890978802, 2810199078, 2732384874, 2657395127, 2585096868, 2515364691, 2448080256, 2383131831, 2320413868, 2259826611, 2201275726, 2144671972, 2089930875, 2036972444, 1985720893, 1936104388, 1888054813, 1841507545, 1796401250, 1752677690, 1710281544, 1669160237, 1629263785, 1590544647, 1552957586, 1516459538, 1481009495, 1446568389, 1413098982, 1380565772, 1348934892, 1318174029, 1288252332, 1259140341, 1230809911, 1203234141, 1176387312, 1150244823, 1124783134, 1099979711, 1075812977, 1052262261, 1029307752, 1006930458, 985112164, 963835394, 943083375, 922840001, 903089802, 883817915, 865010052, 846652474, 828731964, 811235807, 794151760, 777468035, 761173275, 745256537, 729707274, 714515312, 699670838, 685164385, 670986811, 657129292, 643583302, 630340604, 617393236, 604733502, 592353956, 580247397, 568406854, 556825580, 545497042, 534414912, 523573059, 512965541, 502586598, 492430645, 482492264, 472766198, 463247348, 453930763, 444811634, 435885294, 427147207, 418592967, 410218292, 402019018, 393991099, 386130598, 378433686, 370896639, 363515831, 356287735, 349208916, 342276029, 335485819, 328835113, 322320820, 315939929, 309689507, 303566692, 297568696]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 192).prefactor = (1217340498110537/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 192).cutoff/(generalMeanRows 192).c)).2 =
    (416289437808371/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 192).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 192).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 192).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 192

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 192).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 192).criticalRate j.val*(generalMeanRows 192).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 192).c*(generalMeanRows 192).criticalPoint j.val)).2-
      (generalMeanRows 192).J/2-(generalMeanRows 192).error (generalMeanGrid j.val)+
      (generalMeanRows 192).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 192).c)).2-
      (generalMeanRows 192).J/2-(generalMeanRows 192).error 4 := by
  have he : (generalMeanRows 192).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 192) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 192)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0192

/-! Kernel-checked entropy margins for general spectral rectangle 193. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0193
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5151052211, 4978985881, 4814794511, 4658013942, 4508213422, 4364992693, 4227979385, 4096826674, 3971211191, 3850831127, 3735404527, 3624667745, 3518374042, 3416292313, 3318205926, 3223911661, 3133218746, 3045947966, 2961930857, 2881008953, 2803033103, 2727862842, 2655365804, 2585417184, 2517899247, 2452700861, 2389717078, 2328848736, 2270002092, 2213088485, 2158024020, 2104729272, 2053129014, 2003151963, 1954730543, 1907800661, 1862301503, 1818175339, 1775367346, 1733825435, 1693500096, 1654344252, 1616313117, 1579364067, 1543456522, 1508551829, 1474613158, 1441605396, 1409495061, 1378250207, 1347840344, 1318236360, 1289410445, 1261336027, 1233987699, 1207341168, 1181373186, 1156061506, 1131384825, 1107322736, 1083855686, 1060964927, 1038632482, 1016841105, 995574241, 974815996, 954551104, 934764897, 915443274, 896572677, 878140062, 860132877, 842539040, 825346912, 808545284, 792123351, 776070697, 760377275, 745033395, 730029701, 715357164, 701007063, 686970970, 673240744, 659808511, 646666659, 633807824, 621224879, 608910925, 596859283, 585063482, 573517255, 562214526, 551149406, 540316183, 529709318, 519323435, 509153318, 499193902, 489440271, 479887646, 470531388, 461366987, 452390059, 443596343, 434981695, 426542082, 418273582, 410172380, 402234759, 394457102, 386835890, 379367690, 372049162, 364877050, 357848182, 350959466, 344207887, 337590507, 331104459, 324746947]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 193).prefactor = (486713416853361/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 193).cutoff/(generalMeanRows 193).c)).2 =
    (85462208988887/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 193).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 193).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 193).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 193

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 193).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 193).criticalRate j.val*(generalMeanRows 193).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 193).c*(generalMeanRows 193).criticalPoint j.val)).2-
      (generalMeanRows 193).J/2-(generalMeanRows 193).error (generalMeanGrid j.val)+
      (generalMeanRows 193).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 193).c)).2-
      (generalMeanRows 193).J/2-(generalMeanRows 193).error 4 := by
  have he : (generalMeanRows 193).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 193) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 193)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0193

/-! Kernel-checked entropy margins for general spectral rectangle 194. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0194
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5077558501, 4905337659, 4741026368, 4584158910, 4434303061, 4291057162, 4154047509, 4022926013, 3897368095, 3777070790, 3661751040, 3551144144, 3445002351, 3343093587, 3245200287, 3151118339, 3060656112, 2973633565, 2889881437, 2809240500, 2731560865, 2656701355, 2584528921, 2514918097, 2447750510, 2382914414, 2320304268, 2259820335, 2201368320, 2144859028, 2090208045, 2037335450, 1986165532, 1936626544, 1888650458, 1842172747, 1797132176, 1753470610, 1711132832, 1670066374, 1630221361, 1591550360, 1554008243, 1517552056, 1482140900, 1447735814, 1414299668, 1381797063, 1350194240, 1319458984, 1289560547, 1260469567, 1232157996, 1204599025, 1177767029, 1151637494, 1126186969, 1101393004, 1077234103, 1053689676, 1030739988, 1008366122, 986549935, 965274021, 944521673, 924276851, 904524148, 885248761, 866436458, 848073558, 830146898, 812643812, 795552108, 778860044, 762556309, 746630005, 731070624, 715868033, 701012458, 686494467, 672304953, 658435124, 644876487, 631620834, 618660234, 605987015, 593593759, 581473288, 569618656, 558023138, 546680221, 535583598, 524727157, 514104973, 503711303, 493540578, 483587395, 473846512, 464312843, 454981449, 445847534, 436906441, 428153645, 419584749, 411195482, 402981687, 394939326, 387064469, 379353296, 371802088, 364407225, 357165185, 350072538, 343125946, 336322155, 329657998, 323130387, 316736314, 310472849, 304337133, 298326380]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 194).prefactor = (4883110599593203/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 194).cutoff/(generalMeanRows 194).c)).2 =
    (20967143764763/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 194).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 194).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 194).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 194

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 194).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 194).criticalRate j.val*(generalMeanRows 194).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 194).c*(generalMeanRows 194).criticalPoint j.val)).2-
      (generalMeanRows 194).J/2-(generalMeanRows 194).error (generalMeanGrid j.val)+
      (generalMeanRows 194).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 194).c)).2-
      (generalMeanRows 194).J/2-(generalMeanRows 194).error 4 := by
  have he : (generalMeanRows 194).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 194) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 194)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0194

/-! Kernel-checked entropy margins for general spectral rectangle 195. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0195
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5098263446, 4925339065, 4760341552, 4602805343, 4452298301, 4308418796, 4170793097, 4039073042, 3912933933, 3792072651, 3676205951, 3565068910, 3458413534, 3356007482, 3257632902, 3163085380, 3072172967, 2984715295, 2900542766, 2819495806, 2741424177, 2666186347, 2593648911, 2523686045, 2456179019, 2391015731, 2328090284, 2267302591, 2208558009, 2151766997, 2096844805, 2043711177, 1992290075, 1942509428, 1894300895, 1847599638, 1802344122, 1758475916, 1715939514, 1674682169, 1634653732, 1595806503, 1558095095, 1521476304, 1485908985, 1451353940, 1417773810, 1385132973, 1353397452, 1322534825, 1292514141, 1263305842, 1234881688, 1207214692, 1180279048, 1154050074, 1128504153, 1103618675, 1079371993, 1055743366, 1032712918, 1010261595, 988371122, 967023964, 946203293, 925892949, 906077413, 886741770, 867871687, 849453378, 831473584, 813919546, 796778981, 780040062, 763691396, 747722002, 732121299, 716879078, 701985496, 687431052, 673206577, 659303214, 645712410, 632425903, 619435703, 606734087, 594313587, 582166977, 570287263, 558667675, 547301660, 536182869, 525305149, 514662539, 504249260, 494059709, 484088449, 474330208, 464779868, 455432461, 446283164, 437327294, 428560300, 419977761, 411575380, 403348982, 395294504, 387407999, 379685624, 372123643, 364718418, 357466410, 350364172, 343408350, 336595677, 329922968, 323387125, 316985125, 310714025, 304570954, 298553116]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 195).prefactor = (4885470863880931/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 195).cutoff/(generalMeanRows 195).c)).2 =
    (416289437808371/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 195).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 195).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 195).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 195

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 195).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 195).criticalRate j.val*(generalMeanRows 195).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 195).c*(generalMeanRows 195).criticalPoint j.val)).2-
      (generalMeanRows 195).J/2-(generalMeanRows 195).error (generalMeanGrid j.val)+
      (generalMeanRows 195).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 195).c)).2-
      (generalMeanRows 195).J/2-(generalMeanRows 195).error 4 := by
  have he : (generalMeanRows 195).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 195) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 195)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0195

/-! Kernel-checked entropy margins for general spectral rectangle 196. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0196
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5026365757, 4853321261, 4688238102, 4530649109, 4380120620, 4236249562, 4098660834, 3967004964, 3840956014, 3720209677, 3604481572, 3493505696, 3387033017, 3284830199, 3186678440, 3092372412, 3001719289, 2914537861, 2830657721, 2749918516, 2672169259, 2597267699, 2525079734, 2455478875, 2388345746, 2323567624, 2261038014, 2200656252, 2142327139, 2085960597, 2031471359, 1978778668, 1927806005, 1878480834, 1830734365, 1784501329, 1739719770, 1696330855, 1654278691, 1613510154, 1573974733, 1535624379, 1498413369, 1462298173, 1427237333, 1393191349, 1360122570, 1327995095, 1296774676, 1266428631, 1236925756, 1208236254, 1180331651, 1153184736, 1126769488, 1101061017, 1076035507, 1051670159, 1027943138, 1004833528, 982321285, 960387190, 939012812, 918180466, 897873181, 878074660, 858769250, 839941914, 821578194, 803664192, 786186538, 769132368, 752489299, 736245409, 720389213, 704909646, 689796041, 675038116, 660625950, 646549974, 632800952, 619369965, 606248402, 593427943, 580900548, 568658444, 556694116, 545000296, 533569951, 522396273, 511472673, 500792772, 490350387, 480139530, 470154398, 460389365, 450838975, 441497937, 432361117, 423423534, 414680353, 406126880, 397758557, 389570955, 381559773, 373720832, 366050069, 358543533, 351197385, 344007890, 336971415, 330084424, 323343479, 316745231, 310286421, 303963876, 297774506, 291715301, 285783330, 279975736, 274289736]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 196).prefactor = (4901633026847323/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 196).cutoff/(generalMeanRows 196).c)).2 =
    (408384258301257/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 196).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 196).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 196).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 196

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 196).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 196).criticalRate j.val*(generalMeanRows 196).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 196).c*(generalMeanRows 196).criticalPoint j.val)).2-
      (generalMeanRows 196).J/2-(generalMeanRows 196).error (generalMeanGrid j.val)+
      (generalMeanRows 196).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 196).c)).2-
      (generalMeanRows 196).J/2-(generalMeanRows 196).error 4 := by
  have he : (generalMeanRows 196).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 196) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 196)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0196

/-! Kernel-checked entropy margins for general spectral rectangle 197. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0197
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5073424635, 4901350692, 4737194382, 4580488331, 4430798834, 4287722911, 4150885683, 4019938016, 3894554405, 3774431069, 3659284231, 3548848560, 3442875757, 3341133272, 3243403130, 3149480869, 3059174563, 2972303925, 2888699490, 2808201867, 2730661038, 2655935731, 2583892828, 2514406822, 2447359319, 2382638575, 2320139065, 2259761087, 2201410393, 2144997847, 2090439107, 2037654328, 1986567888, 1937108132, 1889207130, 1842800459, 1797826991, 1754228699, 1711950478, 1670939974, 1631147425, 1592525513, 1555029225, 1518615720, 1483244213, 1448875854, 1415473626, 1383002239, 1351428040, 1320718921, 1290844237, 1261774729, 1233482444, 1205940674, 1179123885, 1153007656, 1127568625, 1102784428, 1078633654, 1055095791, 1032151186, 1009780996, 987967153, 966692321, 945939861, 925693800, 905938794, 886660099, 867843545, 849475506, 831542872, 814033031, 796933840, 780233605, 763921061, 747985353, 732416015, 717202955, 702336437, 687807064, 673605767, 659723785, 646152657, 632884206, 619910529, 607223981, 594817171, 582682946, 570814382, 559204776, 547847639, 536736681, 525865809, 515229117, 504820879, 494635542, 484667717, 474912178, 465363850, 456017807, 446869267, 437913582, 429146238, 420562849, 412159150, 403930995, 395874353, 387985303, 380260029, 372694819, 365286061, 358030237, 350923923, 343963784, 337146571, 330469120, 323928349, 317521251, 311244898, 305096436, 299073080]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 197).prefactor = (4896629102670973/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 197).cutoff/(generalMeanRows 197).c)).2 =
    (211202832412903/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 197).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 197).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 197).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 197

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 197).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 197).criticalRate j.val*(generalMeanRows 197).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 197).c*(generalMeanRows 197).criticalPoint j.val)).2-
      (generalMeanRows 197).J/2-(generalMeanRows 197).error (generalMeanGrid j.val)+
      (generalMeanRows 197).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 197).c)).2-
      (generalMeanRows 197).J/2-(generalMeanRows 197).error 4 := by
  have he : (generalMeanRows 197).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 197) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 197)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0197

/-! Kernel-checked entropy margins for general spectral rectangle 198. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0198
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5017438056, 4844690902, 4679921389, 4522659034, 4372467217, 4228940219, 4091700582, 3960396744, 3834700909, 3714307133, 3598929591, 3488301015, 3382171268, 3280306059, 3182485760, 3088504336, 2998168364, 2911296134, 2827716827, 2747269756, 2669803673, 2595176127, 2523252877, 2453907341, 2387020099, 2322478425, 2260175854, 2200011784, 2141891105, 2085723857, 2031424906, 1978913649, 1928113737, 1878952817, 1831362291, 1785277093, 1740635478, 1697378829, 1655451473, 1614800510, 1575375653, 1537129082, 1500015300, 1463991003, 1429014958, 1395047889, 1362052364, 1329992699, 1298834861, 1268546377, 1239096251, 1210454885, 1182594005, 1155486590, 1129106807, 1103429950, 1078432379, 1054091467, 1030385548, 1007293868, 984796538, 962874492, 941509445, 920683856, 900380888, 880584376, 861278796, 842449231, 824081343, 806161344, 788675975, 771612475, 754958562, 738702409, 722832624, 707338228, 692208640, 677433658, 663003438, 648908484, 635139631, 621688026, 608545123, 595702662, 583152661, 570887402, 558899424, 547181507, 535726665, 524528137, 513579375, 502874040, 492405989, 482169270, 472158114, 462366925, 452790281, 443422918, 434259729, 425295760, 416526199, 407946375, 399551750, 391337917, 383300593, 375435616, 367738938, 360206626, 352834854, 345619899, 338558141, 331646056, 324880215, 318257279, 311773999, 305427210, 299213828, 293130851, 287175353, 281344484, 275635464]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 198).prefactor = (2464289504178171/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 198).cutoff/(generalMeanRows 198).c)).2 =
    (414500485318691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 198).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 198).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 198).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 198

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 198).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 198).criticalRate j.val*(generalMeanRows 198).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 198).c*(generalMeanRows 198).criticalPoint j.val)).2-
      (generalMeanRows 198).J/2-(generalMeanRows 198).error (generalMeanGrid j.val)+
      (generalMeanRows 198).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 198).c)).2-
      (generalMeanRows 198).J/2-(generalMeanRows 198).error 4 := by
  have he : (generalMeanRows 198).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 198) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 198)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0198

/-! Kernel-checked entropy margins for general spectral rectangle 199. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0199
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4886997522, 4713822233, 4548676009, 4391088366, 4240622505, 4096872379, 3959460061, 3828033397, 3702263892, 3581844804, 3466489429, 3355929546, 3249914001, 3148207432, 3050589093, 2956851797, 2866800934, 2780253585, 2697037700, 2616991350, 2539962037, 2465806052, 2394387896, 2325579736, 2259260902, 2195317428, 2133641621, 2074131666, 2016691253, 1961229239, 1907659327, 1855899771, 1805873100, 1757505861, 1710728380, 1665474535, 1621681555, 1579289817, 1538242668, 1498486254, 1459969361, 1422643264, 1386461588, 1351380177, 1317356971, 1284351889, 1252326726, 1221245043, 1191072079, 1161774656, 1133321099, 1105681151, 1078825905, 1052727727, 1027360196, 1002698036, 978717060, 955394115, 932707030, 910634563, 889156358, 868252903, 847905481, 828096140, 808807647, 790023462, 771727699, 753905094, 736540980, 719621257, 703132363, 687061253, 671395373, 656122637, 641231408, 626710474, 612549033, 598736673, 585263353, 572119391, 559295445, 546782496, 534571842, 522655076, 511024080, 499671008, 488588278, 477768558, 467204761, 456890029, 446817726, 436981431, 427374928, 417992196, 408827404, 399874905, 391129223, 382585053, 374237249, 366080824, 358110938, 350322897, 342712144, 335274258, 328004946, 320900040, 313955490, 307167365, 300531843, 294045212, 287703861, 281504282, 275443065, 269516891, 263722533, 258056853, 252516795, 247099389, 241801740, 236621033, 231554526]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 199).prefactor = (2467058966572187/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 199).cutoff/(generalMeanRows 199).c)).2 =
    (15710357615927/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 199).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 199).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 199).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 199

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 199).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 199).criticalRate j.val*(generalMeanRows 199).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 199).c*(generalMeanRows 199).criticalPoint j.val)).2-
      (generalMeanRows 199).J/2-(generalMeanRows 199).error (generalMeanGrid j.val)+
      (generalMeanRows 199).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 199).c)).2-
      (generalMeanRows 199).J/2-(generalMeanRows 199).error 4 := by
  have he : (generalMeanRows 199).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 199) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 199)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0199

/-! Kernel-checked entropy margins for general spectral rectangle 200. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0200
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4919385433, 4745062449, 4578821741, 4420189707, 4268726654, 4124023843, 3985700844, 3853403168, 3726800142, 3605582993, 3489463117, 3378170513, 3271452364, 3169071748, 3070806457, 2976447930, 2885800267, 2798679337, 2714911950, 2634335105, 2556795290, 2482147846, 2410256376, 2340992199, 2274233846, 2209866596, 2147782041, 2087877691, 2030056600, 1974227019, 1920302080, 1868199494, 1817841279, 1769153492, 1722065999, 1676512241, 1632429029, 1589756345, 1548437162, 1508417268, 1469645110, 1432071639, 1395650174, 1360336265, 1326087575, 1292863757, 1260626351, 1229338679, 1198965747, 1169474160, 1140832030, 1113008903, 1085975677, 1059704537, 1034168886, 1009343281, 985203374, 961725860, 938888419, 916669669, 895049121, 874007131, 853524859, 833584234, 814167910, 795259235, 776842219, 758901497, 741422305, 724390449, 707792277, 691614658, 675844955, 660471001, 645481082, 630863912, 616608618, 602704719, 589142107, 575911035, 563002099, 550406223, 538114644, 526118902, 514410823, 502982510, 491826330, 480934904, 470301097, 459918005, 449778950, 439877466, 430207297, 420762382, 411536852, 402525021, 393721379, 385120583, 376717456, 368506975, 360484270, 352644614, 344983422, 337496243, 330178754, 323026761, 316036188, 309203075, 302523577, 295993956, 289610579, 283369914, 277268526, 271303077, 265470318, 259767089, 254190316, 248737006, 243404248, 238189206, 233089122]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 200).prefactor = (993363625748037/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 200).cutoff/(generalMeanRows 200).c)).2 =
    (15710357615927/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 200).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 200).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 200).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 200

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 200).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 200).criticalRate j.val*(generalMeanRows 200).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 200).c*(generalMeanRows 200).criticalPoint j.val)).2-
      (generalMeanRows 200).J/2-(generalMeanRows 200).error (generalMeanGrid j.val)+
      (generalMeanRows 200).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 200).c)).2-
      (generalMeanRows 200).J/2-(generalMeanRows 200).error 4 := by
  have he : (generalMeanRows 200).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 200) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 200)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0200

/-! Kernel-checked entropy margins for general spectral rectangle 201. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0201
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5007601100, 4835204395, 4670798688, 4513910320, 4364099839, 4220959010, 4084108141, 3953193696, 3827886137, 3707877990, 3592882095, 3482630018, 3376870618, 3275368739, 3177904018, 3084269801, 2994272148, 2907728931, 2824468991, 2744331382, 2667164661, 2592826246, 2521181816, 2452104759, 2385475666, 2321181859, 2259116958, 2199180470, 2141277423, 2085318013, 2031217285, 1978894828, 1928274500, 1879284164, 1831855450, 1785923526, 1741426887, 1698307158, 1656508915, 1615979504, 1576668890, 1538529499, 1501516082, 1465585582, 1430697007, 1396811322, 1363891331, 1331901583, 1300808271, 1270579146, 1241183430, 1212591739, 1184776006, 1157709413, 1131366323, 1105722221, 1080753652, 1056438170, 1032754282, 1009681403, 987199806, 965290583, 943935601, 923117463, 902819475, 883025609, 863720468, 844889262, 826517774, 808592332, 791099787, 774027485, 757363246, 741095340, 725212469, 709703745, 694558670, 679767125, 665319344, 651205905, 637417713, 623945986, 610782238, 597918273, 585346167, 573058257, 561047135, 549305631, 537826807, 526603945, 515630543, 504900299, 494407111, 484145061, 474108414, 464291609, 454689252, 445296108, 436107099, 427117293, 418321904, 409716283, 401295913, 393056407, 384993500, 377103046, 369381016, 361823490, 354426655, 347186802, 340100324, 333163706, 326373531, 319726469, 313219278, 306848802, 300611965, 294505771, 288527299, 282673704, 276942213]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 201).prefactor = (990922776845597/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 201).cutoff/(generalMeanRows 201).c)).2 =
    (26290896930817/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 201).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 201).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 201).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 201

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 201).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 201).criticalRate j.val*(generalMeanRows 201).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 201).c*(generalMeanRows 201).criticalPoint j.val)).2-
      (generalMeanRows 201).J/2-(generalMeanRows 201).error (generalMeanGrid j.val)+
      (generalMeanRows 201).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 201).c)).2-
      (generalMeanRows 201).J/2-(generalMeanRows 201).error 4 := by
  have he : (generalMeanRows 201).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 201) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 201)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0201

/-! Kernel-checked entropy margins for general spectral rectangle 202. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0202
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5072154445, 4897535362, 4731010289, 4572099461, 4420357763, 4275371695, 4136756672, 4004154599, 3877231692, 3755676511, 3639198195, 3527524851, 3420402099, 3317591752, 3218870606, 3124029343, 3032871525, 2945212673, 2860879423, 2779708754, 2701547272, 2626250555, 2553682551, 2483715017, 2416227003, 2351104381, 2288239396, 2227530263, 2168880783, 2112199997, 2057401853, 2004404903, 1953132025, 1903510151, 1855470030, 1808945994, 1763875745, 1720200157, 1677863090, 1636811212, 1596993841, 1558362793, 1520872234, 1484478551, 1449140225, 1414817717, 1381473352, 1349071221, 1317577083, 1286958273, 1257183615, 1228223346, 1200049039, 1172633528, 1145950847, 1119976165, 1094685725, 1070056790, 1046067592, 1022697278, 999925869, 977734213, 956103942, 935017436, 914457786, 894408755, 874854751, 855780790, 837172474, 819015954, 801297911, 784005529, 767126470, 750648853, 734561235, 718852587, 703512276, 688530051, 673896023, 659600647, 645634711, 631989318, 618655876, 605626080, 592891906, 580445592, 568279634, 556386769, 544759970, 533392434, 522277573, 511409005, 500780548, 490386209, 480220180, 470276826, 460550684, 451036452, 441728986, 432623293, 423714522, 414997965, 406469048, 398123325, 389956479, 381964309, 374142733, 366487782, 358995594, 351662412, 344484581, 337458543, 330580835, 323848085, 317257010, 310804412, 304487175, 298302266, 292246725, 286317671, 280512295]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 202).prefactor = (1003696833341713/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 202).cutoff/(generalMeanRows 202).c)).2 =
    (26290896930817/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 202).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 202).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 202).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 202

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 202).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 202).criticalRate j.val*(generalMeanRows 202).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 202).c*(generalMeanRows 202).criticalPoint j.val)).2-
      (generalMeanRows 202).J/2-(generalMeanRows 202).error (generalMeanGrid j.val)+
      (generalMeanRows 202).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 202).c)).2-
      (generalMeanRows 202).J/2-(generalMeanRows 202).error 4 := by
  have he : (generalMeanRows 202).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 202) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 202)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0202

/-! Kernel-checked entropy margins for general spectral rectangle 203. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0203
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5050176226, 4876301918, 4710457303, 4552168831, 4400997031, 4256533536, 4118398428, 3986237848, 3859721863, 3738542532, 3622412166, 3511061752, 3404239522, 3301709655, 3203251090, 3108656449, 3017731046, 2930291985, 2846167333, 2765195355, 2687223815, 2612109334, 2539716793, 2469918786, 2402595113, 2337632313, 2274923225, 2214366591, 2155866683, 2099332950, 2044679705, 1991825819, 1940694444, 1891212755, 1843311706, 1796925808, 1751992912, 1708454019, 1666253091, 1625336885, 1585654786, 1547158661, 1509802716, 1473543365, 1438339106, 1404150405, 1370939589, 1338670739, 1307309600, 1276823487, 1247181202, 1218352955, 1190310286, 1163025998, 1136474091, 1110629695, 1085469018, 1060969285, 1037108688, 1013866337, 991222215, 969157130, 947652679, 926691205, 906255763, 886330081, 866898535, 847946109, 829458373, 811421448, 793821989, 776647152, 759884575, 743522352, 727549018, 711953523, 696725217, 681853829, 667329454, 653142533, 639283839, 625744465, 612515806, 599589549, 586957660, 574612373, 562546174, 550751799, 539222216, 527950619, 516930418, 506155232, 495618878, 485315366, 475238887, 465383813, 455744682, 446316198, 437093221, 428070763, 419243982, 410608175, 402158777, 393891349, 385801583, 377885287, 370138390, 362556930, 355137058, 347875026, 340767191, 333810006, 327000018, 320333869, 313808286, 307420085, 301166162, 295043494, 289049137, 283180222, 277433952]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 203).prefactor = (4960737383266547/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 203).cutoff/(generalMeanRows 203).c)).2 =
    (414500485318691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 203).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 203).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 203).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 203

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 203).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 203).criticalRate j.val*(generalMeanRows 203).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 203).c*(generalMeanRows 203).criticalPoint j.val)).2-
      (generalMeanRows 203).J/2-(generalMeanRows 203).error (generalMeanGrid j.val)+
      (generalMeanRows 203).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 203).c)).2-
      (generalMeanRows 203).J/2-(generalMeanRows 203).error 4 := by
  have he : (generalMeanRows 203).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 203) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 203)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0203

/-! Kernel-checked entropy margins for general spectral rectangle 204. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0204
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4994919280, 4820402359, 4653975440, 4495161791, 4343518961, 4198635785, 4060129707, 3927644389, 3800847556, 3679429056, 3563099112, 3451586731, 3344638273, 3242016139, 3143497582, 3048873619, 2957948044, 2870536511, 2786465705, 2705572576, 2627703638, 2552714313, 2480468342, 2410837229, 2343699735, 2278941400, 2216454115, 2156135712, 2097889590, 2041624366, 1987253554, 1934695260, 1883871906, 1834709963, 1787139713, 1741095022, 1696513122, 1653334423, 1611502317, 1570963015, 1531665379, 1493560774, 1456602924, 1420747781, 1385953400, 1352179821, 1319388961, 1287544512, 1256611841, 1226557903, 1197351154, 1168961472, 1141360077, 1114519470, 1088413354, 1063016581, 1038305089, 1014255844, 990846792, 968056805, 945865640, 924253887, 903202935, 882694928, 862712730, 843239888, 824260603, 805759692, 787722565, 770135194, 752984087, 736256261, 719939223, 704020943, 688489834, 673334732, 658544880, 644109903, 630019799, 616264914, 602835937, 589723873, 576920042, 564416055, 552203807, 540275466, 528623456, 517240453, 506119371, 495253352, 484635758, 474260163, 464120341, 454210264, 444524087, 435056147, 425800953, 416753181, 407907664, 399259393, 390803503, 382535273, 374450121, 366543596, 358811373, 351249254, 343853155, 336619111, 329543264, 322621864, 315851265, 309227920, 302748377, 296409278, 290207356, 284139428, 278202399, 272393253, 266709052, 261146937, 255704120]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 204).prefactor = (2496552793818881/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 204).cutoff/(generalMeanRows 204).c)).2 =
    (203328653928833/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 204).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 204).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 204).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 204

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 204).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 204).criticalRate j.val*(generalMeanRows 204).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 204).c*(generalMeanRows 204).criticalPoint j.val)).2-
      (generalMeanRows 204).J/2-(generalMeanRows 204).error (generalMeanGrid j.val)+
      (generalMeanRows 204).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 204).c)).2-
      (generalMeanRows 204).J/2-(generalMeanRows 204).error 4 := by
  have he : (generalMeanRows 204).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 204) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 204)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0204

/-! Kernel-checked entropy margins for general spectral rectangle 205. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0205
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4867452125, 4692538721, 4525767863, 4366662658, 4214780332, 4069709250, 3931066260, 3798494313, 3671660319, 3550253226, 3433982276, 3322575432, 3215777950, 3113351080, 3015070883, 2920727153, 2830122432, 2743071104, 2659398569, 2578940483, 2501542057, 2427057416, 2355349002, 2286287027, 2219748968, 2155619097, 2093788047, 2034152408, 1976614357, 1921081310, 1867465597, 1815684166, 1765658300, 1717313359, 1670578539, 1625386640, 1581673862, 1539379601, 1498446268, 1458819116, 1420446078, 1383277613, 1347266569, 1312368048, 1278539281, 1245739509, 1213929877, 1183073330, 1153134514, 1124079687, 1095876632, 1068494578, 1041904122, 1016077159, 990986818, 966607390, 942914278, 919883934, 897493810, 875722305, 854548720, 833953211, 813916751, 794421084, 775448695, 756982767, 739007153, 721506340, 704465423, 687870074, 671706514, 655961492, 640622255, 625676531, 611112501, 596918784, 583084415, 569598826, 556451831, 543633605, 531134673, 518945892, 507058436, 495463787, 484153716, 473120276, 462355787, 451852826, 441604217, 431603021, 421842524, 412316231, 403017858, 393941320, 385080723, 376430363, 367984712, 359738413, 351686274, 343823264, 336144503, 328645259, 321320940, 314167094, 307179397, 300353653, 293685791, 287171855, 280808003, 274590505, 268515736, 262580172, 256780390, 251113062, 245574952, 240162915, 234873889, 229704899, 224653050, 219715523, 214889578]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 205).prefactor = (4999735040435307/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 205).cutoff/(generalMeanRows 205).c)).2 =
    (192518447152133/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 205).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 205).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 205).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 205

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 205).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 205).criticalRate j.val*(generalMeanRows 205).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 205).c*(generalMeanRows 205).criticalPoint j.val)).2-
      (generalMeanRows 205).J/2-(generalMeanRows 205).error (generalMeanGrid j.val)+
      (generalMeanRows 205).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 205).c)).2-
      (generalMeanRows 205).J/2-(generalMeanRows 205).error 4 := by
  have he : (generalMeanRows 205).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 205) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 205)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0205

/-! Kernel-checked entropy margins for general spectral rectangle 206. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0206
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4816530706, 4641057998, 4473787927, 4314240266, 4161969115, 4016559905, 3877626725, 3744809930, 3617773983, 3496205525, 3379811617, 3268318163, 3161468469, 3059021938, 2960752882, 2866449435, 2775912564, 2688955156, 2605401189, 2525084968, 2447850417, 2373550436, 2302046300, 2233207112, 2166909289, 2103036092, 2041477192, 1982128261, 1924890598, 1869670781, 1816380342, 1764935464, 1715256702, 1667268721, 1620900048, 1576082849, 1532752716, 1490848464, 1450311948, 1411087892, 1373123719, 1336369405, 1300777336, 1266302168, 1232900710, 1200531799, 1169156194, 1138736469, 1109236919, 1080623464, 1052863566, 1025926146, 999781510, 974401272, 949758293, 925826612, 902581388, 879998843, 858056207, 836731670, 816004334, 795854166, 776261955, 757209278, 738678453, 720652510, 703115156, 686050737, 669444218, 653281145, 637547622, 622230286, 607316279, 592793229, 578649224, 564872797, 551452898, 538378883, 525640494, 513227837, 501131375, 489341905, 477850548, 466648734, 455728189, 445080921, 434699213, 424575604, 414702886, 405074091, 395682479, 386521530, 377584940, 368866605, 360360617, 352061257, 343962986, 336060440, 328348421, 320821892, 313475970, 306305924, 299307162, 292475235, 285805825, 279294742, 272937920, 266731413, 260671391, 254754134, 248976030, 243333569, 237823344, 232442042, 227186444, 222053423, 217039938, 212143031, 207359828, 202687533, 198123426]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 206).prefactor = (5032870104486217/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 206).cutoff/(generalMeanRows 206).c)).2 =
    (47171752694837/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 206).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 206).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 206).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 206

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 206).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 206).criticalRate j.val*(generalMeanRows 206).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 206).c*(generalMeanRows 206).criticalPoint j.val)).2-
      (generalMeanRows 206).J/2-(generalMeanRows 206).error (generalMeanGrid j.val)+
      (generalMeanRows 206).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 206).c)).2-
      (generalMeanRows 206).J/2-(generalMeanRows 206).error 4 := by
  have he : (generalMeanRows 206).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 206) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 206)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0206

/-! Kernel-checked entropy margins for general spectral rectangle 207. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0207
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5027510517, 4851854895, 4684342060, 4524492171, 4371859891, 4226031369, 4086621556, 3953271788, 3825647621, 3703436880, 3586347897, 3474107912, 3366461629, 3263169898, 3164008519, 3068767147, 2977248293, 2889266410, 2804647052, 2723226106, 2644849082, 2569370461, 2496653094, 2426567647, 2358992089, 2293811214, 2230916207, 2170204234, 2111578062, 2054945715, 2000220140, 1947318910, 1896163939, 1846681221, 1798800581, 1752455454, 1707582663, 1664122227, 1622017172, 1581213356, 1541659308, 1503306075, 1466107080, 1430017986, 1394996576, 1361002628, 1327997812, 1295945582, 1264811079, 1234561043, 1205163724, 1176588802, 1148807312, 1121791573, 1095515118, 1069952634, 1045079903, 1020873739, 997311946, 974373258, 952037297, 930284531, 909096224, 888454405, 868341825, 848741926, 829638802, 811017175, 792862358, 775160232, 757897216, 741060243, 724636739, 708614593, 692982145, 677728159, 662841804, 648312642, 634130601, 620285968, 606769367, 593571750, 580684375, 568098801, 555806869, 543800697, 532072659, 520615384, 509421738, 498484819, 487797947, 477354652, 467148670, 457173930, 447424552, 437894835, 428579252, 419472444, 410569212, 401864511, 393353448, 385031269, 376893362, 368935248, 361152574, 353541112, 346096755, 338815509, 331693493, 324726932, 317912156, 311245594, 304723773, 298343312, 292100923, 285993403, 280017636, 274170586, 268449296, 262850889, 257372558]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 207).prefactor = (251284249529077/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 207).cutoff/(generalMeanRows 207).c)).2 =
    (203328653928833/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 207).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 207).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 207).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 207

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 207).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 207).criticalRate j.val*(generalMeanRows 207).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 207).c*(generalMeanRows 207).criticalPoint j.val)).2-
      (generalMeanRows 207).J/2-(generalMeanRows 207).error (generalMeanGrid j.val)+
      (generalMeanRows 207).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 207).c)).2-
      (generalMeanRows 207).J/2-(generalMeanRows 207).error 4 := by
  have he : (generalMeanRows 207).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 207) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 207)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0207

/-! Kernel-checked entropy margins for general spectral rectangle 208. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0208
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4972974092, 4796705723, 4628640714, 4468295976, 4315223124, 4169005448, 4029255207, 3895611202, 3767736602, 3645316975, 3528058519, 3415686458, 3307943585, 3204588940, 3105396604, 3010154600, 2918663890, 2830737451, 2746199435, 2664884392, 2586636561, 2511309209, 2438764029, 2368870585, 2301505789, 2236553430, 2173903731, 2113452938, 2055102941, 1998760919, 1944339019, 1891754042, 1840927167, 1791783680, 1744252734, 1698267115, 1653763029, 1610679899, 1568960184, 1528549197, 1489394944, 1451447974, 1414661229, 1378989914, 1344391370, 1310824956, 1278251935, 1246635375, 1215940046, 1186132332, 1157180143, 1129052833, 1101721124, 1075157035, 1049333814, 1024225875, 999808734, 976058958, 952954107, 930472689, 908594106, 887298613, 866567278, 846381935, 826725155, 807580204, 788931011, 770762138, 753058749, 735806579, 718991911, 702601549, 686622793, 671043417, 655851648, 641036143, 626585973, 612490603, 598739873, 585323984, 572233481, 559459239, 546992446, 534824594, 522947463, 511353109, 500033854, 488982274, 478191188, 467653651, 457362939, 447312547, 437496174, 427907719, 418541271, 409391105, 400451668, 391717580, 383183623, 374844737, 366696011, 358732683, 350950129, 343343860, 335909518, 328642871, 321539807, 314596333, 307808566, 301172734, 294685171, 288342309, 282140681, 276076915, 270147730, 264349933, 258680418, 253136161, 247714219, 242411727, 237225894]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 208).prefactor = (5058476970142721/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 208).cutoff/(generalMeanRows 208).c)).2 =
    (39887516741561/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 208).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 208).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 208).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 208

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 208).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 208).criticalRate j.val*(generalMeanRows 208).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 208).c*(generalMeanRows 208).criticalPoint j.val)).2-
      (generalMeanRows 208).J/2-(generalMeanRows 208).error (generalMeanGrid j.val)+
      (generalMeanRows 208).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 208).c)).2-
      (generalMeanRows 208).J/2-(generalMeanRows 208).error 4 := by
  have he : (generalMeanRows 208).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 208) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 208)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0208

/-! Kernel-checked entropy margins for general spectral rectangle 209. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0209
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4848451608, 4671815979, 4503437348, 4342832307, 4189552000, 4043179109, 3903325169, 3769628148, 3641750288, 3519376151, 3402210859, 3289978497, 3182420671, 3079295190, 2980374869, 2885446439, 2794309547, 2706775840, 2622668131, 2541819625, 2464073213, 2389280818, 2317302799, 2248007389, 2181270186, 2116973678, 2055006805, 1995264546, 1937647549, 1882061770, 1828418155, 1776632334, 1726624333, 1678318318, 1631642342, 1586528124, 1542910826, 1500728859, 1459923694, 1420439685, 1382223909, 1345226012, 1309398061, 1274694414, 1241071592, 1208488160, 1176904617, 1146283290, 1116588236, 1087785149, 1059841276, 1032725332, 1006407426, 980858984, 956052687, 931962402, 908563124, 885830915, 863742858, 842276996, 821412292, 801128581, 781406526, 762227579, 743573944, 725428537, 707774956, 690597445, 673880869, 657610677, 641772882, 626354032, 611341185, 596721885, 582484143, 568616414, 555107577, 541946916, 529124104, 516629185, 504452555, 492584951, 481017437, 469741385, 458748465, 448030635, 437580122, 427389421, 417451273, 407758665, 398304810, 389083149, 380087333, 371311218, 362748858, 354394495, 346242554, 338287635, 330524506, 322948095, 315553490, 308335924, 301290780, 294413575, 287699964, 281145729, 274746779, 268499139, 262398955, 256442482, 250626084, 244946229, 239399486, 233982520, 228692091, 223525052, 218478340, 213548980, 208734077, 204030817, 199436462]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 209).prefactor = (5066224766667977/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 209).cutoff/(generalMeanRows 209).c)).2 =
    (47171752694837/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 209).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 209).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 209).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 209

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 209).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 209).criticalRate j.val*(generalMeanRows 209).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 209).c*(generalMeanRows 209).criticalPoint j.val)).2-
      (generalMeanRows 209).J/2-(generalMeanRows 209).error (generalMeanGrid j.val)+
      (generalMeanRows 209).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 209).c)).2-
      (generalMeanRows 209).J/2-(generalMeanRows 209).error 4 := by
  have he : (generalMeanRows 209).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 209) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 209)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0209

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock02 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 2 i) := by
  fin_cases i
  · exact EntropyRow0140.numerical
  · exact EntropyRow0141.numerical
  · exact EntropyRow0142.numerical
  · exact EntropyRow0143.numerical
  · exact EntropyRow0144.numerical
  · exact EntropyRow0145.numerical
  · exact EntropyRow0146.numerical
  · exact EntropyRow0147.numerical
  · exact EntropyRow0148.numerical
  · exact EntropyRow0149.numerical
  · exact EntropyRow0150.numerical
  · exact EntropyRow0151.numerical
  · exact EntropyRow0152.numerical
  · exact EntropyRow0153.numerical
  · exact EntropyRow0154.numerical
  · exact EntropyRow0155.numerical
  · exact EntropyRow0156.numerical
  · exact EntropyRow0157.numerical
  · exact EntropyRow0158.numerical
  · exact EntropyRow0159.numerical
  · exact EntropyRow0160.numerical
  · exact EntropyRow0161.numerical
  · exact EntropyRow0162.numerical
  · exact EntropyRow0163.numerical
  · exact EntropyRow0164.numerical
  · exact EntropyRow0165.numerical
  · exact EntropyRow0166.numerical
  · exact EntropyRow0167.numerical
  · exact EntropyRow0168.numerical
  · exact EntropyRow0169.numerical
  · exact EntropyRow0170.numerical
  · exact EntropyRow0171.numerical
  · exact EntropyRow0172.numerical
  · exact EntropyRow0173.numerical
  · exact EntropyRow0174.numerical
  · exact EntropyRow0175.numerical
  · exact EntropyRow0176.numerical
  · exact EntropyRow0177.numerical
  · exact EntropyRow0178.numerical
  · exact EntropyRow0179.numerical
  · exact EntropyRow0180.numerical
  · exact EntropyRow0181.numerical
  · exact EntropyRow0182.numerical
  · exact EntropyRow0183.numerical
  · exact EntropyRow0184.numerical
  · exact EntropyRow0185.numerical
  · exact EntropyRow0186.numerical
  · exact EntropyRow0187.numerical
  · exact EntropyRow0188.numerical
  · exact EntropyRow0189.numerical
  · exact EntropyRow0190.numerical
  · exact EntropyRow0191.numerical
  · exact EntropyRow0192.numerical
  · exact EntropyRow0193.numerical
  · exact EntropyRow0194.numerical
  · exact EntropyRow0195.numerical
  · exact EntropyRow0196.numerical
  · exact EntropyRow0197.numerical
  · exact EntropyRow0198.numerical
  · exact EntropyRow0199.numerical
  · exact EntropyRow0200.numerical
  · exact EntropyRow0201.numerical
  · exact EntropyRow0202.numerical
  · exact EntropyRow0203.numerical
  · exact EntropyRow0204.numerical
  · exact EntropyRow0205.numerical
  · exact EntropyRow0206.numerical
  · exact EntropyRow0207.numerical
  · exact EntropyRow0208.numerical
  · exact EntropyRow0209.numerical
end SingularValueBounds.KL.Certificates
