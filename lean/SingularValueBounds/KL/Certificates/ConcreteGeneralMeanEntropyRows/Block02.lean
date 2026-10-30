import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 140. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0140
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4976274638) (.branch 2 (.leaf 4798590282) (.leaf 4629235032))) (.branch 5 (.branch 4 (.leaf 4467716315) (.leaf 4313576995)) (.branch 6 (.leaf 4166392280) (.leaf 4025766956)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3891332914) (.leaf 3762746923)) (.branch 10 (.leaf 3639688629) (.leaf 3521858737))) (.branch 13 (.branch 12 (.leaf 3408977382) (.leaf 3300782634)) (.branch 14 (.leaf 3197029153) (.leaf 3097486953))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3001940282) (.branch 17 (.leaf 2910186597) (.leaf 2822035617))) (.branch 20 (.branch 19 (.leaf 2737308470) (.leaf 2655836896)) (.branch 21 (.leaf 2577462520) (.leaf 2502036182)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2429417321) (.leaf 2359473402)) (.branch 25 (.leaf 2292079391) (.leaf 2227117265))) (.branch 28 (.branch 27 (.leaf 2164475566) (.leaf 2104048977)) (.branch 29 (.leaf 2045737934) (.leaf 1989448271)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1935090880) (.branch 32 (.leaf 1882581401) (.leaf 1831839932))) (.branch 35 (.branch 34 (.leaf 1782790761) (.leaf 1735362112)) (.branch 36 (.leaf 1689485908) (.leaf 1645097558)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1602135748) (.leaf 1560542251)) (.branch 40 (.leaf 1520261748) (.leaf 1481241660))) (.branch 43 (.branch 42 (.leaf 1443431993) (.leaf 1406785191)) (.branch 44 (.leaf 1371255999) (.leaf 1336801333))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1303380158) (.branch 47 (.leaf 1270953380) (.leaf 1239483734))) (.branch 50 (.branch 49 (.leaf 1208935688) (.leaf 1179275347)) (.branch 51 (.leaf 1150470365) (.leaf 1122489864)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1095304355) (.leaf 1068885662)) (.branch 55 (.leaf 1043206857) (.leaf 1018242195))) (.branch 58 (.branch 57 (.leaf 993967050) (.leaf 970357856)) (.branch 59 (.leaf 947392060) (.leaf 925048063))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 903305176) (.branch 62 (.leaf 882143572) (.leaf 861544244))) (.branch 65 (.branch 64 (.leaf 841488967) (.leaf 821960254)) (.branch 66 (.leaf 802941325) (.leaf 784416071)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 766369018) (.leaf 748785304)) (.branch 70 (.leaf 731650645) (.leaf 714951306))) (.branch 73 (.branch 72 (.leaf 698674079) (.leaf 682806260)) (.branch 74 (.leaf 667335619) (.leaf 652250383))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 637539215) (.branch 77 (.leaf 623191194) (.leaf 609195795))) (.branch 80 (.branch 79 (.leaf 595542871) (.leaf 582222639)) (.branch 81 (.leaf 569225661) (.leaf 556542832)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 544165362) (.leaf 532084765)) (.branch 85 (.leaf 520292846) (.leaf 508781686))) (.branch 88 (.branch 87 (.leaf 497543634) (.leaf 486571293)) (.branch 89 (.leaf 475857512) (.leaf 465395373)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 455178185) (.branch 92 (.leaf 445199470) (.leaf 435452960))) (.branch 95 (.branch 94 (.leaf 425932585) (.leaf 416632465)) (.branch 96 (.leaf 407546906) (.leaf 398670388)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 389997562) (.leaf 381523243)) (.branch 100 (.leaf 373242401) (.leaf 365150160))) (.branch 103 (.branch 102 (.leaf 357241786) (.leaf 349512688)) (.branch 104 (.leaf 341958409) (.leaf 334574621))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 327357124) (.leaf 320301836)) (.branch 108 (.leaf 313404793) (.leaf 306662145))) (.branch 111 (.branch 110 (.leaf 300070147) (.leaf 293625162)) (.branch 112 (.leaf 287323652) (.leaf 281162179)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 275137398) (.leaf 269246056)) (.branch 116 (.leaf 263484986) (.leaf 257851110))) (.branch 119 (.branch 118 (.leaf 252341431) (.leaf 246953031)) (.branch 120 (.leaf 241683070) (.leaf 236528782)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 140).q*(generalMeanRows 140).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 140).q*(generalMeanRows 140).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5158507339) (.branch 2 (.leaf 4982433128) (.leaf 4814583217))) (.branch 5 (.branch 4 (.leaf 4654464904) (.leaf 4501621277)) (.branch 6 (.leaf 4355628092) (.leaf 4216090973)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4082642900) (.leaf 3954941959)) (.branch 10 (.leaf 3832669308) (.leaf 3715527346))) (.branch 13 (.branch 12 (.leaf 3603238044) (.leaf 3495541447)) (.branch 14 (.leaf 3392194297) (.leaf 3292968784))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3197651414) (.branch 17 (.leaf 3106041962) (.leaf 3017952519))) (.branch 20 (.branch 19 (.leaf 2933206622) (.leaf 2851638447)) (.branch 21 (.leaf 2773092077) (.leaf 2697420818)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2624486575) (.leaf 2554159276)) (.branch 25 (.leaf 2486316336) (.leaf 2420842166))) (.branch 28 (.branch 27 (.leaf 2357627717) (.leaf 2296570055)) (.branch 29 (.leaf 2237571970) (.leaf 2180541611)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2125392153) (.branch 32 (.leaf 2072041475) (.leaf 2020411873))) (.branch 35 (.branch 34 (.leaf 1970429791) (.leaf 1922025558)) (.branch 36 (.leaf 1875133161) (.leaf 1829690022)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1785636791) (.leaf 1742917157)) (.branch 40 (.leaf 1701477664) (.leaf 1661267551))) (.branch 43 (.branch 42 (.leaf 1622238588) (.leaf 1584344935)) (.branch 44 (.leaf 1547543000) (.leaf 1511791315))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1477050413) (.branch 47 (.leaf 1443282717) (.leaf 1410452432))) (.branch 50 (.branch 49 (.leaf 1378525447) (.leaf 1347469242)) (.branch 51 (.leaf 1317252802) (.leaf 1287846532)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1259222180) (.leaf 1231352770)) (.branch 55 (.leaf 1204212526) (.leaf 1177776812))) (.branch 58 (.branch 57 (.leaf 1152022074) (.leaf 1126925779)) (.branch 59 (.leaf 1102466362) (.leaf 1078623179))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1055376458) (.branch 62 (.leaf 1032707252) (.leaf 1010597399))) (.branch 65 (.branch 64 (.leaf 989029486) (.leaf 967986802)) (.branch 66 (.leaf 947453315) (.leaf 927413627)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 907852950) (.leaf 888757076)) (.branch 70 (.leaf 870112344) (.leaf 851905618))) (.branch 73 (.branch 72 (.leaf 834124262) (.leaf 816756113)) (.branch 74 (.leaf 799789461) (.leaf 783213030))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 767015952) (.branch 77 (.leaf 751187753) (.leaf 735718335))) (.branch 80 (.branch 79 (.leaf 720597955) (.leaf 705817214)) (.branch 81 (.leaf 691367038) (.leaf 677238665)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 663423632) (.leaf 649913760)) (.branch 85 (.leaf 636701143) (.leaf 623778138))) (.branch 88 (.branch 87 (.leaf 611137351) (.leaf 598771627)) (.branch 89 (.leaf 586674041) (.leaf 574837888)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 563256675) (.branch 92 (.leaf 551924111) (.leaf 540834099))) (.branch 95 (.branch 94 (.leaf 529980729) (.leaf 519358269)) (.branch 96 (.leaf 508961162) (.leaf 498784014)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 488821591) (.leaf 479068812)) (.branch 100 (.leaf 469520743) (.leaf 460172593))) (.branch 103 (.branch 102 (.leaf 451019705) (.leaf 442057556)) (.branch 104 (.leaf 433281748) (.leaf 424688007))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 416272175) (.leaf 408030209)) (.branch 108 (.leaf 399958173) (.leaf 392052241))) (.branch 111 (.branch 110 (.leaf 384308687) (.leaf 376723881)) (.branch 112 (.leaf 369294294) (.leaf 362016484)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 354887102) (.leaf 347902883)) (.branch 116 (.leaf 341060645) (.leaf 334357289))) (.branch 119 (.branch 118 (.leaf 327789793) (.leaf 321355209)) (.branch 120 (.leaf 315050665) (.leaf 308873358)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 141).q*(generalMeanRows 141).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 141).q*(generalMeanRows 141).cutoff/2-2 = (902/395:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable079.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5191653435) (.branch 2 (.leaf 5014447856) (.leaf 4845519422))) (.branch 5 (.branch 4 (.leaf 4684372265) (.leaf 4530546538)) (.branch 6 (.leaf 4383615272) (.leaf 4243181554)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4108876007) (.leaf 3980354521)) (.branch 10 (.leaf 3857296205) (.leaf 3739401544))) (.branch 13 (.branch 12 (.leaf 3626390726) (.leaf 3518002122)) (.branch 14 (.leaf 3413990912) (.leaf 3314127824))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3218197990) (.branch 17 (.leaf 3125999899) (.leaf 3037344436))) (.branch 20 (.branch 19 (.leaf 2952054002) (.leaf 2869961710)) (.branch 21 (.leaf 2790910638) (.leaf 2714753152)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2641350268) (.leaf 2570571079)) (.branch 25 (.leaf 2502292213) (.leaf 2436397338))) (.branch 28 (.branch 27 (.leaf 2372776703) (.leaf 2311326714)) (.branch 29 (.leaf 2251949535) (.leaf 2194552727)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2139048904) (.branch 32 (.leaf 2085355420) (.leaf 2033394072))) (.branch 35 (.branch 34 (.leaf 1983090828) (.leaf 1934375573)) (.branch 36 (.leaf 1887181868) (.leaf 1841446733)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1797110438) (.leaf 1754116307)) (.branch 40 (.leaf 1712410544) (.leaf 1671942060))) (.branch 43 (.branch 42 (.leaf 1632662316) (.leaf 1594525176)) (.branch 44 (.leaf 1557486770) (.leaf 1521505362))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1486541232) (.branch 47 (.leaf 1452556560) (.leaf 1419515323))) (.branch 50 (.branch 49 (.leaf 1387383191) (.leaf 1356127434)) (.branch 51 (.leaf 1325716837) (.leaf 1296121616)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1267313339) (.leaf 1239264853)) (.branch 55 (.leaf 1211950218) (.leaf 1185344642))) (.branch 58 (.branch 57 (.leaf 1159424416) (.leaf 1134166864)) (.branch 59 (.leaf 1109550283) (.leaf 1085553895))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1062157801) (.branch 62 (.leaf 1039342934) (.leaf 1017091014))) (.branch 65 (.branch 64 (.leaf 995384515) (.leaf 974206622)) (.branch 66 (.leaf 953541196) (.leaf 933372742)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 913686378) (.leaf 894467803)) (.branch 70 (.leaf 875703269) (.leaf 857379555))) (.branch 73 (.branch 72 (.leaf 839483945) (.leaf 822004196)) (.branch 74 (.leaf 804928525) (.leaf 788245582))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 771944429) (.branch 77 (.leaf 756014526) (.leaf 740445708))) (.branch 80 (.branch 79 (.leaf 725228172) (.leaf 710352457)) (.branch 81 (.leaf 695809431) (.leaf 681590276)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 667686474) (.leaf 654089794)) (.branch 85 (.leaf 640792280) (.leaf 627786238))) (.branch 88 (.branch 87 (.leaf 615064227) (.leaf 602619046)) (.branch 89 (.leaf 590443727) (.leaf 578531521)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 566875893) (.branch 92 (.leaf 555470511) (.leaf 544309240))) (.branch 95 (.branch 94 (.leaf 533386131) (.leaf 522695417)) (.branch 96 (.leaf 512231503) (.leaf 501988962)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 491962525) (.leaf 482147079)) (.branch 100 (.leaf 472537659) (.leaf 463129441))) (.branch 103 (.branch 102 (.leaf 453917741) (.leaf 444898006)) (.branch 104 (.leaf 436065809) (.leaf 427416849))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418946941) (.leaf 410652015)) (.branch 108 (.leaf 402528113) (.leaf 394571381))) (.branch 111 (.branch 110 (.leaf 386778070) (.leaf 379144528)) (.branch 112 (.leaf 371667202) (.leaf 364342629)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357167437) (.leaf 350138340)) (.branch 116 (.leaf 343252138) (.leaf 336505709))) (.branch 119 (.branch 118 (.leaf 329896013) (.leaf 323420084)) (.branch 120 (.leaf 317075030) (.leaf 310858031)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 142).q*(generalMeanRows 142).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 142).q*(generalMeanRows 142).cutoff/2-2 = (902/395:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable079.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4785520765) (.branch 2 (.leaf 4607335862) (.leaf 4437607720))) (.branch 5 (.branch 4 (.leaf 4275836841) (.leaf 4121559570)) (.branch 6 (.leaf 3974344971) (.leaf 3833792029)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3699527156) (.leaf 3571201933)) (.branch 10 (.leaf 3448491090) (.leaf 3331090674))) (.branch 13 (.branch 12 (.leaf 3218716395) (.leaf 3111102122)) (.branch 14 (.leaf 3007998516) (.leaf 2909171789))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2814402569) (.branch 17 (.leaf 2723484857) (.leaf 2636225085))) (.branch 20 (.branch 19 (.leaf 2552441239) (.leaf 2471962063)) (.branch 21 (.leaf 2394626319) (.leaf 2320282113)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2248786271) (.leaf 2180003758)) (.branch 25 (.leaf 2113807152) (.leaf 2050076144))) (.branch 28 (.branch 27 (.leaf 1988697088) (.leaf 1929562572)) (.branch 29 (.leaf 1872571031) (.leaf 1817626378)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1764637669) (.branch 32 (.leaf 1713518785) (.leaf 1664188140))) (.branch 35 (.branch 34 (.leaf 1616568407) (.leaf 1570586264)) (.branch 36 (.leaf 1526172156) (.leaf 1483260075)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1441787348) (.leaf 1401694449)) (.branch 40 (.leaf 1362924814) (.leaf 1325424673))) (.branch 43 (.branch 42 (.leaf 1289142892) (.leaf 1254030823)) (.branch 44 (.leaf 1220042165) (.leaf 1187132834))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1155260843) (.branch 47 (.leaf 1124386180) (.leaf 1094470708))) (.branch 50 (.branch 49 (.leaf 1065478059) (.leaf 1037373539)) (.branch 51 (.leaf 1010124042) (.leaf 983697960)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 958065110) (.leaf 933196655)) (.branch 55 (.leaf 909065034) (.leaf 885643900))) (.branch 58 (.branch 57 (.leaf 862908053) (.leaf 840833383)) (.branch 59 (.leaf 819396816) (.leaf 798576260))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 778350555) (.branch 62 (.leaf 758699431) (.leaf 739603457))) (.branch 65 (.branch 64 (.leaf 721044007) (.leaf 703003216)) (.branch 66 (.leaf 685463944) (.leaf 668409741)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 651824816) (.leaf 635694003)) (.branch 70 (.leaf 620002733) (.leaf 604737004))) (.branch 73 (.branch 72 (.leaf 589883358) (.leaf 575428853)) (.branch 74 (.leaf 561361039) (.leaf 547667938))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 534338022) (.branch 77 (.leaf 521360189) (.leaf 508723749))) (.branch 80 (.branch 79 (.leaf 496418403) (.leaf 484434226)) (.branch 81 (.leaf 472761652) (.leaf 461391455)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 450314740) (.leaf 439522921)) (.branch 85 (.leaf 429007716) (.leaf 418761128))) (.branch 88 (.branch 87 (.leaf 408775436) (.leaf 399043184)) (.branch 89 (.leaf 389557168) (.leaf 380310427)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 371296230) (.branch 92 (.leaf 362508074) (.leaf 353939667))) (.branch 95 (.branch 94 (.leaf 345584924) (.leaf 337437957)) (.branch 96 (.leaf 329493067) (.leaf 321744740)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 314187636) (.leaf 306816583)) (.branch 100 (.leaf 299626573) (.leaf 292612751))) (.branch 103 (.branch 102 (.leaf 285770415) (.leaf 279095008)) (.branch 104 (.leaf 272582110) (.leaf 266227436))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 260026831) (.leaf 253976265)) (.branch 108 (.leaf 248071827) (.leaf 242309722))) (.branch 111 (.branch 110 (.leaf 236686266) (.leaf 231197885)) (.branch 112 (.leaf 225841108) (.leaf 220612564)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 215508980) (.leaf 210527175)) (.branch 116 (.leaf 205664060) (.leaf 200916633))) (.branch 119 (.branch 118 (.leaf 196281978) (.leaf 191757258)) (.branch 120 (.leaf 187339718) (.leaf 183026677)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 143).q*(generalMeanRows 143).c/2-2 = (361/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable083.value]
    have hcontinuation : (generalMeanRows 143).q*(generalMeanRows 143).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5291937287) (.branch 2 (.leaf 5121006341) (.leaf 4957948209))) (.branch 5 (.branch 4 (.leaf 4802289177) (.leaf 4653590113)) (.branch 6 (.leaf 4511443444) (.leaf 4375470449)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4245318827) (.leaf 4120660519)) (.branch 10 (.leaf 4001189740) (.leaf 3886621204))) (.branch 13 (.branch 12 (.leaf 3776688514) (.leaf 3671142703)) (.branch 14 (.leaf 3569750909) (.leaf 3472295165))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3378571296) (.branch 17 (.leaf 3288387913) (.leaf 3201565489))) (.branch 20 (.branch 19 (.leaf 3117935515) (.leaf 3037339721)) (.branch 21 (.leaf 2959629365) (.leaf 2884664577)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2812313748) (.leaf 2742452979)) (.branch 25 (.leaf 2674965559) (.leaf 2609741495))) (.branch 28 (.branch 27 (.leaf 2546677065) (.leaf 2485674410)) (.branch 29 (.leaf 2426641159) (.leaf 2369490077)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2314138734) (.branch 32 (.leaf 2260509208) (.leaf 2208527800))) (.branch 35 (.branch 34 (.leaf 2158124771) (.leaf 2109234102)) (.branch 36 (.leaf 2061793260) (.leaf 2015742992)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1971027124) (.leaf 1927592379)) (.branch 40 (.leaf 1885388201) (.leaf 1844366595))) (.branch 43 (.branch 42 (.leaf 1804481979) (.leaf 1765691040)) (.branch 44 (.leaf 1727952607) (.leaf 1691227520))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1655478522) (.branch 47 (.leaf 1620670146) (.leaf 1586768617))) (.branch 50 (.branch 49 (.leaf 1553741755) (.leaf 1521558886)) (.branch 51 (.leaf 1490190759) (.leaf 1459609467)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1429788372) (.leaf 1400702041)) (.branch 55 (.leaf 1372326173) (.leaf 1344637545))) (.branch 58 (.branch 57 (.leaf 1317613950) (.leaf 1291234146)) (.branch 59 (.leaf 1265477801) (.leaf 1240325451))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1215758449) (.branch 62 (.leaf 1191758927) (.leaf 1168309753))) (.branch 65 (.branch 64 (.leaf 1145394497) (.leaf 1122997391)) (.branch 66 (.leaf 1101103298) (.leaf 1079697680)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1058766570) (.leaf 1038296541)) (.branch 70 (.leaf 1018274681) (.leaf 998688568))) (.branch 73 (.branch 72 (.leaf 979526245) (.leaf 960776201)) (.branch 74 (.leaf 942427346) (.leaf 924468993))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 906890840) (.branch 77 (.leaf 889682951) (.leaf 872835737))) (.branch 80 (.branch 79 (.leaf 856339945) (.leaf 840186640)) (.branch 81 (.leaf 824367189) (.leaf 808873251)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 793696762) (.leaf 778829924)) (.branch 85 (.leaf 764265192) (.leaf 749995264))) (.branch 88 (.branch 87 (.leaf 736013071) (.leaf 722311767)) (.branch 89 (.leaf 708884720) (.leaf 695725500)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 682827875) (.branch 92 (.leaf 670185803) (.leaf 657793419))) (.branch 95 (.branch 94 (.leaf 645645033) (.leaf 633735123)) (.branch 96 (.leaf 622058325) (.leaf 610609429)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 599383373) (.leaf 588375239)) (.branch 100 (.leaf 577580244) (.leaf 566993737))) (.branch 103 (.branch 102 (.leaf 556611194) (.leaf 546428215)) (.branch 104 (.leaf 536440516) (.leaf 526643927))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 517034388) (.leaf 507607945)) (.branch 108 (.leaf 498360746) (.leaf 489289038))) (.branch 111 (.branch 110 (.leaf 480389162) (.leaf 471657552)) (.branch 112 (.leaf 463090732) (.leaf 454685311)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 446437981) (.leaf 438345515)) (.branch 116 (.leaf 430404765) (.leaf 422612657))) (.branch 119 (.branch 118 (.leaf 414966192) (.leaf 407462439)) (.branch 120 (.leaf 400098540) (.leaf 392871699)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 144).q*(generalMeanRows 144).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7666569635) (.branch 2 (.leaf 7424066346) (.leaf 7191741514))) (.branch 5 (.branch 4 (.leaf 6969048332) (.leaf 6755477747)) (.branch 6 (.leaf 6550555073) (.leaf 6353836989)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6164908879) (.leaf 5983382445)) (.branch 10 (.leaf 5808893580) (.leaf 5641100456))) (.branch 13 (.branch 12 (.leaf 5479681799) (.leaf 5324335341)) (.branch 14 (.leaf 5174776405) (.leaf 5030736639))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4891962845) (.branch 17 (.leaf 4758215930) (.leaf 4629269938))) (.branch 20 (.branch 19 (.leaf 4504911165) (.leaf 4384937350)) (.branch 21 (.leaf 4269156931) (.leaf 4157388364)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4049459485) (.leaf 3945206936)) (.branch 25 (.leaf 3844475619) (.leaf 3747118207))) (.branch 28 (.branch 27 (.leaf 3652994674) (.leaf 3561971871)) (.branch 29 (.leaf 3473923125) (.leaf 3388727872)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3306271307) (.branch 32 (.leaf 3226444068) (.leaf 3149141928))) (.branch 35 (.branch 34 (.leaf 3074265522) (.leaf 3001720076)) (.branch 36 (.leaf 2931415169) (.leaf 2863264496)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2797185656) (.leaf 2733099946)) (.branch 40 (.leaf 2670932173) (.leaf 2610610473))) (.branch 43 (.branch 42 (.leaf 2552066140) (.leaf 2495233474)) (.branch 44 (.leaf 2440049625) (.leaf 2386454453))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2334390398) (.branch 47 (.leaf 2283802350) (.leaf 2234637536))) (.branch 50 (.branch 49 (.leaf 2186845402) (.leaf 2140377511)) (.branch 51 (.leaf 2095187440) (.leaf 2051230688)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2008464583) (.leaf 1966848201)) (.branch 55 (.leaf 1926342281) (.leaf 1886909151))) (.branch 58 (.branch 57 (.leaf 1848512654) (.leaf 1811118081)) (.branch 59 (.leaf 1774692106) (.leaf 1739202719))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1704619174) (.branch 62 (.leaf 1670911928) (.leaf 1638052590))) (.branch 65 (.branch 64 (.leaf 1606013870) (.leaf 1574769529)) (.branch 66 (.leaf 1544294338) (.leaf 1514564028)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1485555253) (.leaf 1457245548)) (.branch 70 (.leaf 1429613295) (.leaf 1402637680))) (.branch 73 (.branch 72 (.leaf 1376298667) (.leaf 1350576961)) (.branch 74 (.leaf 1325453975) (.leaf 1300911805))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1276933198) (.branch 77 (.leaf 1253501529) (.leaf 1230600770))) (.branch 80 (.branch 79 (.leaf 1208215468) (.leaf 1186330722)) (.branch 81 (.leaf 1164932161) (.leaf 1144005919)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1123538621) (.leaf 1103517355)) (.branch 85 (.leaf 1083929660) (.leaf 1064763505))) (.branch 88 (.branch 87 (.leaf 1046007274) (.leaf 1027649747)) (.branch 89 (.leaf 1009680085) (.leaf 992087817)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 974862824) (.branch 92 (.leaf 957995325) (.leaf 941475864))) (.branch 95 (.branch 94 (.leaf 925295300) (.leaf 909444790)) (.branch 96 (.leaf 893915782) (.leaf 878700001)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 863789441) (.leaf 849176353)) (.branch 100 (.leaf 834853235) (.leaf 820812824))) (.branch 103 (.branch 102 (.leaf 807048087) (.leaf 793552212)) (.branch 104 (.leaf 780318599) (.leaf 767340853))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 754612777) (.leaf 742128364)) (.branch 108 (.leaf 729881789) (.leaf 717867407))) (.branch 111 (.branch 110 (.leaf 706079738) (.leaf 694513471)) (.branch 112 (.leaf 683163449) (.leaf 672024672)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 661092282) (.leaf 650361567)) (.branch 116 (.leaf 639827950) (.leaf 629486986))) (.branch 119 (.branch 118 (.leaf 619334359) (.leaf 609365874)) (.branch 120 (.leaf 599577455) (.leaf 589965142)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 145).q*(generalMeanRows 145).c/2-2 = (117/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable009.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6431762543) (.branch 2 (.leaf 6244529767) (.leaf 6065383708))) (.branch 5 (.branch 4 (.leaf 5893870999) (.leaf 5729569891)) (.branch 6 (.leaf 5572087484) (.leaf 5421057246)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5276136814) (.leaf 5137006018)) (.branch 10 (.leaf 5003365105) (.leaf 4874933143))) (.branch 13 (.branch 12 (.leaf 4751446579) (.leaf 4632657933)) (.branch 14 (.leaf 4518334611) (.leaf 4408257829))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4302221632) (.branch 17 (.leaf 4200031995) (.leaf 4101506000))) (.branch 20 (.branch 19 (.leaf 4006471089) (.leaf 3914764367)) (.branch 21 (.leaf 3826231970) (.leaf 3740728477)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3658116372) (.leaf 3578265542)) (.branch 25 (.leaf 3501052816) (.leaf 3426361539))) (.branch 28 (.branch 27 (.leaf 3354081169) (.leaf 3284106917)) (.branch 29 (.leaf 3216339396) (.leaf 3150684307)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3087052139) (.branch 32 (.leaf 3025357895) (.leaf 2965520829))) (.branch 35 (.branch 34 (.leaf 2907464208) (.leaf 2851115084)) (.branch 36 (.leaf 2796404085) (.leaf 2743265212)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2691635659) (.leaf 2641455636)) (.branch 40 (.leaf 2592668207) (.leaf 2545219134))) (.branch 43 (.branch 42 (.leaf 2499056736) (.leaf 2454131754)) (.branch 44 (.leaf 2410397217) (.leaf 2367808333))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2326322364) (.branch 47 (.leaf 2285898530) (.leaf 2246497902))) (.branch 50 (.branch 49 (.leaf 2208083309) (.leaf 2170619251)) (.branch 51 (.leaf 2134071810) (.leaf 2098408575)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2063598566) (.leaf 2029612159)) (.branch 55 (.leaf 1996421025) (.leaf 1963998060))) (.branch 58 (.branch 57 (.leaf 1932317330) (.leaf 1901354011)) (.branch 59 (.leaf 1871084338) (.leaf 1841485550))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1812535845) (.branch 62 (.leaf 1784214333) (.leaf 1756500993))) (.branch 65 (.branch 64 (.leaf 1729376629) (.leaf 1702822836)) (.branch 66 (.leaf 1676821961) (.leaf 1651357064)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1626411890) (.leaf 1601970835)) (.branch 70 (.leaf 1578018917) (.leaf 1554541744))) (.branch 73 (.branch 72 (.leaf 1531525491) (.leaf 1508956872)) (.branch 74 (.leaf 1486823118) (.leaf 1465111950))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1443811558) (.branch 77 (.leaf 1422910583) (.leaf 1402398092))) (.branch 80 (.branch 79 (.leaf 1382263563) (.leaf 1362496866)) (.branch 81 (.leaf 1343088243) (.leaf 1324028297)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1305307968) (.leaf 1286918529)) (.branch 85 (.leaf 1268851562) (.leaf 1251098949))) (.branch 88 (.branch 87 (.leaf 1233652860) (.leaf 1216505739)) (.branch 89 (.leaf 1199650291) (.leaf 1183079474)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1166786488) (.branch 92 (.leaf 1150764761) (.leaf 1135007944))) (.branch 95 (.branch 94 (.leaf 1119509899) (.leaf 1104264692)) (.branch 96 (.leaf 1089266583) (.leaf 1074510020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1059989629) (.leaf 1045700207)) (.branch 100 (.leaf 1031636718) (.leaf 1017794282))) (.branch 103 (.branch 102 (.leaf 1004168174) (.leaf 990753812)) (.branch 104 (.leaf 977546756) (.leaf 964542698))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 951737463) (.leaf 939126997)) (.branch 108 (.leaf 926707368) (.leaf 914474756))) (.branch 111 (.branch 110 (.leaf 902425455) (.leaf 890555862)) (.branch 112 (.leaf 878862477) (.leaf 867341901)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 855990825) (.leaf 844806036)) (.branch 116 (.leaf 833784405) (.leaf 822922891))) (.branch 119 (.branch 118 (.leaf 812218530) (.leaf 801668441)) (.branch 120 (.leaf 791269816) (.leaf 781019921)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 146).q*(generalMeanRows 146).c/2-2 = (39/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable085.value]
    have hcontinuation : (generalMeanRows 146).q*(generalMeanRows 146).cutoff/2-2 = (224/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable086.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6560513340) (.branch 2 (.leaf 6365963151) (.leaf 6179821105))) (.branch 5 (.branch 4 (.leaf 6001616623) (.leaf 5830911934)) (.branch 6 (.leaf 5667299194) (.leaf 5510397923)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5359852713) (.leaf 5215331183)) (.branch 10 (.leaf 5076522132) (.leaf 4943133887))) (.branch 13 (.branch 12 (.leaf 4814892804) (.leaf 4691541912)) (.branch 14 (.leaf 4572839685) (.leaf 4458558921))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4348485729) (.branch 17 (.leaf 4242418590) (.leaf 4140167512))) (.branch 20 (.branch 19 (.leaf 4041553245) (.leaf 3946406566)) (.branch 21 (.leaf 3854567620) (.leaf 3765885311)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3680216740) (.leaf 3597426690)) (.branch 25 (.leaf 3517387147) (.leaf 3439976852))) (.branch 28 (.branch 27 (.leaf 3365080894) (.leaf 3292590325)) (.branch 29 (.leaf 3222401802) (.leaf 3154417264)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3088543614) (.branch 32 (.leaf 3024692439) (.leaf 2962779739))) (.branch 35 (.branch 34 (.leaf 2902725675) (.leaf 2844454338)) (.branch 36 (.leaf 2787893527) (.leaf 2732974543)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2679632001) (.leaf 2627803645)) (.branch 40 (.leaf 2577430181) (.leaf 2528455117))) (.branch 43 (.branch 42 (.leaf 2480824614) (.leaf 2434487346)) (.branch 44 (.leaf 2389394367) (.leaf 2345498985))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2302756651) (.branch 47 (.leaf 2261124841) (.leaf 2220562957))) (.branch 50 (.branch 49 (.leaf 2181032225) (.leaf 2142495608)) (.branch 51 (.leaf 2104917712) (.leaf 2068264710)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2032504257) (.leaf 1997605423)) (.branch 55 (.leaf 1963538619) (.leaf 1930275533))) (.branch 58 (.branch 57 (.leaf 1897789066) (.leaf 1866053276)) (.branch 59 (.leaf 1835043317) (.leaf 1804735394))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1775106703) (.branch 62 (.leaf 1746135393) (.leaf 1717800513))) (.branch 65 (.branch 64 (.leaf 1690081975) (.leaf 1662960511)) (.branch 66 (.leaf 1636417636) (.leaf 1610435608)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1584997398) (.leaf 1560086654)) (.branch 70 (.leaf 1535687672) (.leaf 1511785364))) (.branch 73 (.branch 72 (.leaf 1488365231) (.leaf 1465413338)) (.branch 74 (.leaf 1442916285) (.leaf 1420861186))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1399235643) (.branch 77 (.leaf 1378027729) (.leaf 1357225961))) (.branch 80 (.branch 79 (.leaf 1336819285) (.leaf 1316797054)) (.branch 81 (.leaf 1297149013) (.leaf 1277865280)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1258936329) (.leaf 1240352978)) (.branch 85 (.leaf 1222106371) (.leaf 1204187964))) (.branch 88 (.branch 87 (.leaf 1186589514) (.leaf 1169303065)) (.branch 89 (.leaf 1152320934) (.leaf 1135635703)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1119240205) (.branch 92 (.leaf 1103127515) (.leaf 1087290940))) (.branch 95 (.branch 94 (.leaf 1071724009) (.leaf 1056420462)) (.branch 96 (.leaf 1041374245) (.leaf 1026579499)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1012030554) (.leaf 997721920)) (.branch 100 (.leaf 983648278) (.leaf 969804478))) (.branch 103 (.branch 102 (.leaf 956185527) (.leaf 942786588)) (.branch 104 (.leaf 929602969) (.leaf 916630120))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 903863627) (.leaf 891299208)) (.branch 108 (.leaf 878932706) (.leaf 866760082))) (.branch 111 (.branch 110 (.leaf 854777419) (.leaf 842980906)) (.branch 112 (.leaf 831366845) (.leaf 819931638)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 808671788) (.leaf 797583895)) (.branch 116 (.leaf 786664650) (.leaf 775910834))) (.branch 119 (.branch 118 (.leaf 765319316) (.leaf 754887046)) (.branch 120 (.leaf 744611052) (.leaf 734488445)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 147).q*(generalMeanRows 147).c/2-2 = (41/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable058.value]
    have hcontinuation : (generalMeanRows 147).q*(generalMeanRows 147).cutoff/2-2 = (224/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable086.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6692777244) (.branch 2 (.leaf 6490698033) (.leaf 6297361346))) (.branch 5 (.branch 4 (.leaf 6112278680) (.leaf 5934995578)) (.branch 6 (.leaf 5765088636) (.leaf 5602162845)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5445849208) (.leaf 5295802621)) (.branch 10 (.leaf 5151699956) (.leaf 5013238347))) (.branch 13 (.branch 12 (.leaf 4880133632) (.leaf 4752118947)) (.branch 14 (.leaf 4628943455) (.leaf 4510371178))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4396179948) (.branch 17 (.leaf 4286160433) (.leaf 4180115261))) (.branch 20 (.branch 19 (.leaf 4077858203) (.leaf 3979213434)) (.branch 21 (.leaf 3884014847) (.leaf 3792105423)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3703336647) (.leaf 3617567977)) (.branch 25 (.leaf 3534666339) (.leaf 3454505672))) (.branch 28 (.branch 27 (.leaf 3376966499) (.leaf 3301935531)) (.branch 29 (.leaf 3229305298) (.leaf 3158973803)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3090844208) (.branch 32 (.leaf 3024824533) (.leaf 2960827374))) (.branch 35 (.branch 34 (.leaf 2898769652) (.leaf 2838572360)) (.branch 36 (.leaf 2780160343) (.leaf 2723462083)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2668409497) (.leaf 2614937754)) (.branch 40 (.leaf 2562985095) (.leaf 2512492672))) (.branch 43 (.branch 42 (.leaf 2463404392) (.leaf 2415666768)) (.branch 44 (.leaf 2369228788) (.leaf 2324041781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2280059297) (.branch 47 (.leaf 2237236994) (.leaf 2195532528))) (.branch 50 (.branch 49 (.leaf 2154905453) (.leaf 2115317124)) (.branch 51 (.leaf 2076730605) (.leaf 2039110587)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2002423305) (.leaf 1966636459)) (.branch 55 (.leaf 1931719149) (.leaf 1897641797))) (.branch 58 (.branch 57 (.leaf 1864376090) (.leaf 1831894916)) (.branch 59 (.leaf 1800172307) (.leaf 1769183381))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1738904294) (.branch 62 (.leaf 1709312190) (.leaf 1680385149))) (.branch 65 (.branch 64 (.leaf 1652102153) (.leaf 1624443033)) (.branch 66 (.leaf 1597388436) (.leaf 1570919787)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1545019249) (.leaf 1519669691)) (.branch 70 (.leaf 1494854659) (.leaf 1470558339))) (.branch 73 (.branch 72 (.leaf 1446765531) (.leaf 1423461625)) (.branch 74 (.leaf 1400632566) (.leaf 1378264837))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1356345429) (.branch 77 (.leaf 1334861824) (.leaf 1313801969))) (.branch 80 (.branch 79 (.leaf 1293154257) (.leaf 1272907508)) (.branch 81 (.leaf 1253050949) (.leaf 1233574197)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1214467243) (.leaf 1195720436)) (.branch 85 (.leaf 1177324463) (.leaf 1159270344))) (.branch 88 (.branch 87 (.leaf 1141549406) (.leaf 1124153281)) (.branch 89 (.leaf 1107073887) (.leaf 1090303417)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1073834327) (.branch 92 (.leaf 1057659327) (.leaf 1041771371))) (.branch 95 (.branch 94 (.leaf 1026163643) (.leaf 1010829552)) (.branch 96 (.leaf 995762720) (.leaf 980956974)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 966406340) (.leaf 952105030)) (.branch 100 (.leaf 938047441) (.leaf 924228142))) (.branch 103 (.branch 102 (.leaf 910641872) (.leaf 897283528)) (.branch 104 (.leaf 884148163) (.leaf 871230981))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 858527326) (.leaf 846032680)) (.branch 108 (.leaf 833742658) (.leaf 821653003))) (.branch 111 (.branch 110 (.leaf 809759579) (.leaf 798058368)) (.branch 112 (.leaf 786545467) (.leaf 775217081)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 764069520) (.leaf 753099197)) (.branch 116 (.leaf 742302621) (.leaf 731676397))) (.branch 119 (.branch 118 (.leaf 721217219) (.leaf 710921870)) (.branch 120 (.leaf 700787217) (.leaf 690810210)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 148).q*(generalMeanRows 148).c/2-2 = (43/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable048.value]
    have hcontinuation : (generalMeanRows 148).q*(generalMeanRows 148).cutoff/2-2 = (224/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable086.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6248086250) (.branch 2 (.leaf 6039934606) (.leaf 5840904062))) (.branch 5 (.branch 4 (.leaf 5650488707) (.leaf 5468217782)) (.branch 6 (.leaf 5293652580) (.leaf 5126383704)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4966028611) (.leaf 4812229414)) (.branch 10 (.leaf 4664650914) (.leaf 4522978819))) (.branch 13 (.branch 12 (.leaf 4386918144) (.leaf 4256191758)) (.branch 14 (.leaf 4130539070) (.leaf 4009714827))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3893488029) (.branch 17 (.leaf 3781640927) (.leaf 3673968118))) (.branch 20 (.branch 19 (.leaf 3570275703) (.leaf 3470380525)) (.branch 21 (.leaf 3374109460) (.leaf 3281298772)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3191793508) (.leaf 3105446949)) (.branch 25 (.leaf 3022120097) (.leaf 2941681196))) (.branch 28 (.branch 27 (.leaf 2864005299) (.leaf 2788973854)) (.branch 29 (.leaf 2716474328) (.leaf 2646399850)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2578648886) (.branch 32 (.leaf 2513124927) (.leaf 2449736207))) (.branch 35 (.branch 34 (.leaf 2388395434) (.leaf 2329019538)) (.branch 36 (.leaf 2271529441) (.leaf 2215849833)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2161908968) (.leaf 2109638476)) (.branch 40 (.leaf 2058973175) (.leaf 2009850906))) (.branch 43 (.branch 42 (.leaf 1962212370) (.leaf 1916000984)) (.branch 44 (.leaf 1871162732) (.leaf 1827646037))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1785401637) (.branch 47 (.leaf 1744382463) (.leaf 1704543529))) (.branch 50 (.branch 49 (.leaf 1665841830) (.leaf 1628236241)) (.branch 51 (.leaf 1591687421) (.leaf 1556157729)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1521611139) (.leaf 1488013161)) (.branch 55 (.leaf 1455330765) (.leaf 1423532314))) (.branch 58 (.branch 57 (.leaf 1392587494) (.leaf 1362467251)) (.branch 59 (.leaf 1333143733) (.leaf 1304590233))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1276781134) (.branch 62 (.leaf 1249691857) (.leaf 1223298816))) (.branch 65 (.branch 64 (.leaf 1197579370) (.leaf 1172511780)) (.branch 66 (.leaf 1148075167) (.leaf 1124249474)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1101015427) (.leaf 1078354502)) (.branch 70 (.leaf 1056248890) (.leaf 1034681465))) (.branch 73 (.branch 72 (.leaf 1013635754) (.leaf 993095907)) (.branch 74 (.leaf 973046672) (.leaf 953473366))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 934361853) (.branch 77 (.leaf 915698518) (.leaf 897470245))) (.branch 80 (.branch 79 (.leaf 879664397) (.leaf 862268794)) (.branch 81 (.leaf 845271693) (.leaf 828661773)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 812428111) (.leaf 796560173)) (.branch 85 (.leaf 781047792) (.leaf 765881154))) (.branch 88 (.branch 87 (.leaf 751050786) (.leaf 736547538)) (.branch 89 (.leaf 722362573) (.leaf 708487353)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 694913628) (.branch 92 (.leaf 681633420) (.leaf 668639021))) (.branch 95 (.branch 94 (.leaf 655922971) (.leaf 643478059)) (.branch 96 (.leaf 631297305) (.leaf 619373956)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 607701473) (.leaf 596273527)) (.branch 100 (.leaf 585083989) (.leaf 574126921))) (.branch 103 (.branch 102 (.leaf 563396570) (.leaf 552887361)) (.branch 104 (.leaf 542593891) (.leaf 532510922))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 522633372) (.leaf 512956315)) (.branch 108 (.leaf 503474970) (.leaf 494184699))) (.branch 111 (.branch 110 (.leaf 485080999) (.leaf 476159500)) (.branch 112 (.leaf 467415957) (.leaf 458846251)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 450446377) (.leaf 442212446)) (.branch 116 (.leaf 434140677) (.leaf 426227397))) (.branch 119 (.branch 118 (.leaf 418469035) (.leaf 410862117)) (.branch 120 (.leaf 403403266) (.leaf 396089196)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 149).q*(generalMeanRows 149).c/2-2 = (11/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable087.value]
    have hcontinuation : (generalMeanRows 149).q*(generalMeanRows 149).cutoff/2-2 = (224/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable086.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6170875258) (.branch 2 (.leaf 5981473352) (.leaf 5800390216))) (.branch 5 (.branch 4 (.leaf 5627153277) (.leaf 5461323156)) (.branch 6 (.leaf 5302490763) (.leaf 5150274714)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5004319013) (.leaf 4864290987)) (.branch 10 (.leaf 4729879417) (.leaf 4600792862))) (.branch 13 (.branch 12 (.leaf 4476758136) (.leaf 4357518939)) (.branch 14 (.leaf 4242834600) (.leaf 4132478945))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4026239260) (.branch 17 (.leaf 3923915339) (.leaf 3825318621))) (.branch 20 (.branch 19 (.leaf 3730271394) (.leaf 3638606062)) (.branch 21 (.leaf 3550164475) (.leaf 3464797306)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3382363486) (.leaf 3302729669)) (.branch 25 (.leaf 3225769748) (.leaf 3151364399))) (.branch 28 (.branch 27 (.leaf 3079400666) (.leaf 3009771567)) (.branch 29 (.leaf 2942375733) (.leaf 2877117073)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2813904459) (.branch 32 (.leaf 2752651435) (.leaf 2693275942))) (.branch 35 (.branch 34 (.leaf 2635700065) (.leaf 2579849796)) (.branch 36 (.leaf 2525654808) (.leaf 2473048254)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2421966563) (.leaf 2372349265)) (.branch 40 (.leaf 2324138817) (.leaf 2277280440))) (.branch 43 (.branch 42 (.leaf 2231721974) (.leaf 2187413730)) (.branch 44 (.leaf 2144308362) (.leaf 2102360739))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2061527828) (.branch 47 (.leaf 2021768584) (.leaf 1983043845))) (.branch 50 (.branch 49 (.leaf 1945316234) (.leaf 1908550065)) (.branch 51 (.leaf 1872711260) (.leaf 1837767261)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1803686955) (.leaf 1770440603)) (.branch 55 (.leaf 1737999766) (.leaf 1706337243))) (.branch 58 (.branch 57 (.leaf 1675427009) (.leaf 1645244153)) (.branch 59 (.leaf 1615764830) (.leaf 1586966201))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1558826389) (.branch 62 (.leaf 1531324427) (.leaf 1504440221))) (.branch 65 (.branch 64 (.leaf 1478154502) (.leaf 1452448788)) (.branch 66 (.leaf 1427305348) (.leaf 1402707163)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1378637897) (.leaf 1355081861)) (.branch 70 (.leaf 1332023983) (.leaf 1309449782))) (.branch 73 (.branch 72 (.leaf 1287345338) (.leaf 1265697265)) (.branch 74 (.leaf 1244492691) (.leaf 1223719232))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1203364967) (.branch 77 (.leaf 1183418422) (.leaf 1163868546))) (.branch 80 (.branch 79 (.leaf 1144704696) (.leaf 1125916613)) (.branch 81 (.leaf 1107494411) (.leaf 1089428557)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1071709858) (.leaf 1054329442)) (.branch 85 (.leaf 1037278748) (.leaf 1020549512))) (.branch 88 (.branch 87 (.leaf 1004133752) (.leaf 988023759)) (.branch 89 (.leaf 972212083) (.leaf 956691523)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 941455116) (.branch 92 (.leaf 926496129) (.leaf 911808046))) (.branch 95 (.branch 94 (.leaf 897384563) (.leaf 883219576)) (.branch 96 (.leaf 869307175) (.leaf 855641634)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 842217407) (.leaf 829029117)) (.branch 100 (.leaf 816071552) (.leaf 803339656))) (.branch 103 (.branch 102 (.leaf 790828526) (.leaf 778533404)) (.branch 104 (.leaf 766449671) (.leaf 754572844))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 742898566) (.leaf 731422608)) (.branch 108 (.leaf 720140859) (.leaf 709049323))) (.branch 111 (.branch 110 (.leaf 698144116) (.leaf 687421459)) (.branch 112 (.leaf 676877678) (.leaf 666509196)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 656312534) (.leaf 646284303)) (.branch 116 (.leaf 636421204) (.leaf 626720024))) (.branch 119 (.branch 118 (.leaf 617177631) (.leaf 607790976)) (.branch 120 (.leaf 598557084) (.leaf 589473057)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 150).q*(generalMeanRows 150).c/2-2 = (29/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable045.value]
    have hcontinuation : (generalMeanRows 150).q*(generalMeanRows 150).cutoff/2-2 = (554/287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable088.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5638460902) (.branch 2 (.leaf 5444969620) (.leaf 5260133239))) (.branch 5 (.branch 4 (.leaf 5083464053) (.leaf 4914508454)) (.branch 6 (.leaf 4752843951) (.leaf 4598076512)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4449838191) (.leaf 4307784997)) (.branch 10 (.leaf 4171594982) (.leaf 4040966515))) (.branch 13 (.branch 12 (.leaf 3915616726) (.leaf 3795280090)) (.branch 14 (.leaf 3679707148) (.leaf 3568663337))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3461927930) (.branch 17 (.leaf 3359293058) (.leaf 3260562826))) (.branch 20 (.branch 19 (.leaf 3165552495) (.leaf 3074087731)) (.branch 21 (.leaf 2986003918) (.leaf 2901145521)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2819365503) (.leaf 2740524778)) (.branch 25 (.leaf 2664491718) (.leaf 2591141682))) (.branch 28 (.branch 27 (.leaf 2520356591) (.leaf 2452024526)) (.branch 29 (.leaf 2386039357) (.leaf 2322300399)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2260712091) (.branch 32 (.leaf 2201183695) (.leaf 2143629017))) (.branch 35 (.branch 34 (.leaf 2087966147) (.leaf 2034117215)) (.branch 36 (.leaf 1982008161) (.leaf 1931568525)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1882731245) (.leaf 1835432470)) (.branch 40 (.leaf 1789611386) (.leaf 1745210050))) (.branch 43 (.branch 42 (.leaf 1702173235) (.leaf 1660448285)) (.branch 44 (.leaf 1619984979) (.leaf 1580735403))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1542653828) (.branch 47 (.leaf 1505696597) (.leaf 1469822017))) (.branch 50 (.branch 49 (.leaf 1434990259) (.leaf 1401163263)) (.branch 51 (.leaf 1368304646) (.leaf 1336379621)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1305354914) (.leaf 1275198690)) (.branch 55 (.leaf 1245880481) (.leaf 1217371118))) (.branch 58 (.branch 57 (.leaf 1189642671) (.leaf 1162668383)) (.branch 59 (.leaf 1136422617) (.leaf 1110880801))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1086019377) (.branch 62 (.leaf 1061815753) (.leaf 1038248256))) (.branch 65 (.branch 64 (.leaf 1015296091) (.leaf 992939297)) (.branch 66 (.leaf 971158709) (.leaf 949935924)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 929253260) (.leaf 909093730)) (.branch 70 (.leaf 889441003) (.leaf 870279379))) (.branch 73 (.branch 72 (.leaf 851593761) (.leaf 833369624)) (.branch 74 (.leaf 815592991) (.leaf 798250412))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 781328935) (.branch 77 (.leaf 764816089) (.leaf 748699860))) (.branch 80 (.branch 79 (.leaf 732968672) (.leaf 717611368)) (.branch 81 (.leaf 702617194) (.leaf 687975778)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 673677114) (.leaf 659711553)) (.branch 85 (.leaf 646069778) (.leaf 632742798))) (.branch 88 (.branch 87 (.leaf 619721930) (.leaf 606998791)) (.branch 89 (.leaf 594565278) (.leaf 582413564)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 570536084) (.branch 92 (.leaf 558925524) (.leaf 547574808))) (.branch 95 (.branch 94 (.leaf 536477097) (.leaf 525625771)) (.branch 96 (.leaf 515014423) (.leaf 504636854)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 494487059) (.leaf 484559225)) (.branch 100 (.leaf 474847720) (.leaf 465347088))) (.branch 103 (.branch 102 (.leaf 456052040) (.leaf 446957452)) (.branch 104 (.leaf 438058354) (.leaf 429349927))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 420827496) (.leaf 412486526)) (.branch 108 (.leaf 404322617) (.leaf 396331496))) (.branch 111 (.branch 110 (.leaf 388509017) (.leaf 380851155)) (.branch 112 (.leaf 373353997) (.leaf 366013746)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358826711) (.leaf 351789304)) (.branch 116 (.leaf 344898040) (.leaf 338149530))) (.branch 119 (.branch 118 (.leaf 331540479) (.leaf 325067680)) (.branch 120 (.leaf 318728018) (.leaf 312518458)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 151).q*(generalMeanRows 151).c/2-2 = (187/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable062.value]
    have hcontinuation : (generalMeanRows 151).q*(generalMeanRows 151).cutoff/2-2 = (554/287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable088.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5628124114) (.branch 2 (.leaf 5453128331) (.leaf 5285930931))) (.branch 5 (.branch 4 (.leaf 5126080525) (.leaf 4973157784)) (.branch 6 (.leaf 4826772643) (.leaf 4686561806)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4552186510) (.leaf 4423330523)) (.branch 10 (.leaf 4299698336) (.leaf 4181013538))) (.branch 13 (.branch 12 (.leaf 4067017340) (.leaf 3957467242)) (.branch 14 (.leaf 3852135816) (.leaf 3750809603))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3653288103) (.branch 17 (.leaf 3559382855) (.leaf 3468916591))) (.branch 20 (.branch 19 (.leaf 3381722465) (.leaf 3297643335)) (.branch 21 (.leaf 3216531118) (.leaf 3138246179)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3062656780) (.leaf 2989638565)) (.branch 25 (.leaf 2919074083) (.leaf 2850852351))) (.branch 28 (.branch 27 (.leaf 2784868445) (.leaf 2721023123)) (.branch 29 (.leaf 2659222470) (.leaf 2599377577)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2541404232) (.branch 32 (.leaf 2485222641) (.leaf 2430757163))) (.branch 35 (.branch 34 (.leaf 2377936060) (.leaf 2326691277)) (.branch 36 (.leaf 2276958216) (.leaf 2228675545)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2181785004) (.leaf 2136231235)) (.branch 40 (.leaf 2091961612) (.leaf 2048926092))) (.branch 43 (.branch 42 (.leaf 2007077068) (.leaf 1966369234)) (.branch 44 (.leaf 1926759458) (.leaf 1888206663))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1850671715) (.branch 47 (.leaf 1814117317) (.leaf 1778507911))) (.branch 50 (.branch 49 (.leaf 1743809584) (.leaf 1709989980)) (.branch 51 (.leaf 1677018218) (.leaf 1644864816)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1613501614) (.leaf 1582901709)) (.branch 55 (.leaf 1553039387) (.leaf 1523890064))) (.branch 58 (.branch 57 (.leaf 1495430225) (.leaf 1467637374)) (.branch 59 (.leaf 1440489977) (.leaf 1413967419))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1388049953) (.branch 62 (.leaf 1362718660) (.leaf 1337955407))) (.branch 65 (.branch 64 (.leaf 1313742808) (.leaf 1290064185)) (.branch 66 (.leaf 1266903540) (.leaf 1244245513)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1222075360) (.leaf 1200378917)) (.branch 70 (.leaf 1179142576) (.leaf 1158353255))) (.branch 73 (.branch 72 (.leaf 1137998377) (.leaf 1118065846)) (.branch 74 (.leaf 1098544020) (.leaf 1079421695))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1060688083) (.branch 77 (.leaf 1042332791) (.leaf 1024345808))) (.branch 80 (.branch 79 (.leaf 1006717481) (.leaf 989438503)) (.branch 81 (.leaf 972499899) (.leaf 955893007)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 939609466) (.leaf 923641204)) (.branch 85 (.leaf 907980423) (.leaf 892619589))) (.branch 88 (.branch 87 (.leaf 877551420) (.leaf 862768876)) (.branch 89 (.leaf 848265145) (.leaf 834033641)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 820067984) (.branch 92 (.leaf 806362003) (.leaf 792909716))) (.branch 95 (.branch 94 (.leaf 779705332) (.leaf 766743237)) (.branch 96 (.leaf 754017988) (.leaf 741524310)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 729257082) (.leaf 717211339)) (.branch 100 (.leaf 705382259) (.leaf 693765163))) (.branch 103 (.branch 102 (.leaf 682355504) (.leaf 671148867)) (.branch 104 (.leaf 660140961) (.leaf 649327615))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 638704774) (.leaf 628268494)) (.branch 108 (.leaf 618014938) (.leaf 607940373))) (.branch 111 (.branch 110 (.leaf 598041164) (.leaf 588313775)) (.branch 112 (.leaf 578754759) (.leaf 569360760)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 560128509) (.leaf 551054819)) (.branch 116 (.leaf 542136583) (.leaf 533370773))) (.branch 119 (.branch 118 (.leaf 524754434) (.leaf 516284686)) (.branch 120 (.leaf 507958717) (.leaf 499773783)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 152).q*(generalMeanRows 152).c/2-2 = (311/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable072.value]
    have hcontinuation : (generalMeanRows 152).q*(generalMeanRows 152).cutoff/2-2 = (1096/533:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable089.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5304960183) (.branch 2 (.leaf 5126193145) (.leaf 4955502900))) (.branch 5 (.branch 4 (.leaf 4792424906) (.leaf 4636527493)) (.branch 6 (.leaf 4487408990) (.leaf 4344695170)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4208036959) (.leaf 4077108383)) (.branch 10 (.leaf 3951604717) (.leaf 3831240817))) (.branch 13 (.branch 12 (.leaf 3715749614) (.leaf 3604880739)) (.branch 14 (.leaf 3498399287) (.leaf 3396084680))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3297729635) (.branch 17 (.leaf 3203139223) (.leaf 3112130001))) (.branch 20 (.branch 19 (.leaf 3024529220) (.leaf 2940174100)) (.branch 21 (.leaf 2858911156) (.leaf 2780595585)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2705090693) (.leaf 2632267371)) (.branch 25 (.leaf 2562003610) (.leaf 2494184048))) (.branch 28 (.branch 27 (.leaf 2428699556) (.leaf 2365446848)) (.branch 29 (.leaf 2304328123) (.leaf 2245250730)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2188126860) (.branch 32 (.leaf 2132873250) (.leaf 2079410920))) (.branch 35 (.branch 34 (.leaf 2027664916) (.leaf 1977564079)) (.branch 36 (.leaf 1929040821) (.leaf 1882030925)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1836473348) (.leaf 1792310044)) (.branch 40 (.leaf 1749485796) (.leaf 1707948056))) (.branch 43 (.branch 42 (.leaf 1667646799) (.leaf 1628534384)) (.branch 44 (.leaf 1590565423) (.leaf 1553696659))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1517886851) (.branch 47 (.leaf 1483096667) (.leaf 1449288579))) (.branch 50 (.branch 49 (.leaf 1416426774) (.leaf 1384477055)) (.branch 51 (.leaf 1353406764) (.leaf 1323184699)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1293781038) (.leaf 1265167270)) (.branch 55 (.leaf 1237316126) (.leaf 1210201518))) (.branch 58 (.branch 57 (.leaf 1183798480) (.leaf 1158083106)) (.branch 59 (.leaf 1133032506) (.leaf 1108624748))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1084838814) (.branch 62 (.leaf 1061654557) (.leaf 1039052654))) (.branch 65 (.branch 64 (.leaf 1017014569) (.leaf 995522515)) (.branch 66 (.leaf 974559418) (.leaf 954108883)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 934155160) (.leaf 914683116)) (.branch 70 (.leaf 895678206) (.leaf 877126444))) (.branch 73 (.branch 72 (.leaf 859014378) (.leaf 841329067)) (.branch 74 (.leaf 824058054) (.leaf 807189349))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 790711401) (.branch 77 (.leaf 774613086) (.leaf 758883684))) (.branch 80 (.branch 79 (.leaf 743512859) (.leaf 728490646)) (.branch 81 (.leaf 713807434) (.leaf 699453949)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 685421240) (.leaf 671700667)) (.branch 85 (.leaf 658283883) (.leaf 645162828))) (.branch 88 (.branch 87 (.leaf 632329712) (.leaf 619777006)) (.branch 89 (.leaf 607497430) (.leaf 595483943)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 583729734) (.branch 92 (.leaf 572228213) (.leaf 560972999))) (.branch 95 (.branch 94 (.leaf 549957915) (.leaf 539176979)) (.branch 96 (.leaf 528624395) (.leaf 518294546)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 508181991) (.leaf 498281451)) (.branch 100 (.leaf 488587808) (.leaf 479096098))) (.branch 103 (.branch 102 (.leaf 469801503) (.leaf 460699350)) (.branch 104 (.leaf 451785101) (.leaf 443054348))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 434502813) (.leaf 426126339)) (.branch 108 (.leaf 417920886) (.leaf 409882529))) (.branch 111 (.branch 110 (.leaf 402007452) (.leaf 394291945)) (.branch 112 (.leaf 386732400) (.leaf 379325306)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 372067249) (.leaf 364954907)) (.branch 116 (.leaf 357985044) (.leaf 351154512))) (.branch 119 (.branch 118 (.leaf 344460247) (.leaf 337899261)) (.branch 120 (.leaf 331468648) (.leaf 325165573)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 153).q*(generalMeanRows 153).c/2-2 = (737/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable090.value]
    have hcontinuation : (generalMeanRows 153).q*(generalMeanRows 153).cutoff/2-2 = (1096/533:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable089.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5359684207) (.branch 2 (.leaf 5187870041) (.leaf 5023794697))) (.branch 5 (.branch 4 (.leaf 4867006687) (.leaf 4717086778)) (.branch 6 (.leaf 4573645177) (.leaf 4436319019)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4304770119) (.leaf 4178682947)) (.branch 10 (.leaf 4057762812) (.leaf 3941734217))) (.branch 13 (.branch 12 (.leaf 3830339377) (.leaf 3723336868)) (.branch 14 (.leaf 3620500401) (.leaf 3521617708))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3426489526) (.branch 17 (.leaf 3334928661) (.leaf 3246759141))) (.branch 20 (.branch 19 (.leaf 3161815431) (.leaf 3079941718)) (.branch 21 (.leaf 3000991247) (.leaf 2924825718)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2851314720) (.leaf 2780335217)) (.branch 25 (.leaf 2711771065) (.leaf 2645512574))) (.branch 28 (.branch 27 (.leaf 2581456091) (.leaf 2519503626)) (.branch 29 (.leaf 2459562494) (.leaf 2401544986)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2345368067) (.branch 32 (.leaf 2290953090) (.leaf 2238225528))) (.branch 35 (.branch 34 (.leaf 2187114735) (.leaf 2137553705)) (.branch 36 (.leaf 2089478867) (.leaf 2042829879)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1997549440) (.leaf 1953583116)) (.branch 40 (.leaf 1910879177) (.leaf 1869388439))) (.branch 43 (.branch 42 (.leaf 1829064125) (.leaf 1789861725)) (.branch 44 (.leaf 1751738874) (.leaf 1714655229))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1678572360) (.branch 47 (.leaf 1643453645) (.leaf 1609264171))) (.branch 50 (.branch 49 (.leaf 1575970641) (.leaf 1543541289)) (.branch 51 (.leaf 1511945795) (.leaf 1481155212)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1451141890) (.leaf 1421879409)) (.branch 55 (.leaf 1393342517) (.leaf 1365507064))) (.branch 58 (.branch 57 (.leaf 1338349952) (.leaf 1311849076)) (.branch 59 (.leaf 1285983274) (.leaf 1260732280))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1236076679) (.branch 62 (.leaf 1211997865) (.leaf 1188477998))) (.branch 65 (.branch 64 (.leaf 1165499968) (.leaf 1143047360)) (.branch 66 (.leaf 1121104415) (.leaf 1099656007)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1078687602) (.leaf 1058185238)) (.branch 70 (.leaf 1038135491) (.leaf 1018525456))) (.branch 73 (.branch 72 (.leaf 999342716) (.leaf 980575324)) (.branch 74 (.leaf 962211778) (.leaf 944241002))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 926652326) (.branch 77 (.leaf 909435468) (.leaf 892580515))) (.branch 80 (.branch 79 (.leaf 876077906) (.leaf 859918420)) (.branch 81 (.leaf 844093154) (.leaf 828593518)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 813411212) (.leaf 798538220)) (.branch 85 (.leaf 783966794) (.leaf 769689445))) (.branch 88 (.branch 87 (.leaf 755698930) (.leaf 741988243)) (.branch 89 (.leaf 728550603) (.leaf 715379447)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 702468419) (.branch 92 (.leaf 689811364) (.leaf 677402317))) (.branch 95 (.branch 94 (.leaf 665235497) (.leaf 653305298)) (.branch 96 (.leaf 641606284) (.leaf 630133182)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 618880875) (.leaf 607844394)) (.branch 100 (.leaf 597018917) (.leaf 586399758))) (.branch 103 (.branch 102 (.leaf 575982368) (.leaf 565762322)) (.branch 104 (.leaf 555735322) (.leaf 545897189))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 536243856) (.leaf 526771369)) (.branch 108 (.leaf 517475881) (.leaf 508353645))) (.branch 111 (.branch 110 (.leaf 499401017) (.leaf 490614445)) (.branch 112 (.leaf 481990471) (.leaf 473525728)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 465216931) (.leaf 457060883)) (.branch 116 (.leaf 449054463) (.leaf 441194632))) (.branch 119 (.branch 118 (.leaf 433478423) (.leaf 425902943)) (.branch 120 (.leaf 418465371) (.leaf 411162951)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 154).q*(generalMeanRows 154).c/2-2 = (271/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable076.value]
    have hcontinuation : (generalMeanRows 154).q*(generalMeanRows 154).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5382302796) (.branch 2 (.leaf 5212670066) (.leaf 5050720682))) (.branch 5 (.branch 4 (.leaf 4896001015) (.leaf 4748090079)) (.branch 6 (.leaf 4606596681) (.leaf 4471156872)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4341431672) (.leaf 4217105022)) (.branch 10 (.leaf 4097881935) (.leaf 3983486833))) (.branch 13 (.branch 12 (.leaf 3873662038) (.leaf 3768166405)) (.branch 14 (.leaf 3666774078) (.leaf 3569273357))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3475465664) (.branch 17 (.leaf 3385164602) (.leaf 3298195084))) (.branch 20 (.branch 19 (.leaf 3214392542) (.leaf 3133602200)) (.branch 21 (.leaf 3055678403) (.leaf 2980483998)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2907889765) (.leaf 2837773893)) (.branch 25 (.leaf 2770021495) (.leaf 2704524155))) (.branch 28 (.branch 27 (.leaf 2641179515) (.leaf 2579890887)) (.branch 29 (.leaf 2520566896) (.leaf 2463121149)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2407471920) (.branch 32 (.leaf 2353541869) (.leaf 2301257770))) (.branch 35 (.branch 34 (.leaf 2250550265) (.leaf 2201353626)) (.branch 36 (.leaf 2153605542) (.leaf 2107246917)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2062221676) (.leaf 2018476595)) (.branch 40 (.leaf 1975961128) (.leaf 1934627257))) (.branch 43 (.branch 42 (.leaf 1894429347) (.leaf 1855324008)) (.branch 44 (.leaf 1817269968) (.leaf 1780227955))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1744160586) (.branch 47 (.leaf 1709032259) (.leaf 1674809056))) (.branch 50 (.branch 49 (.leaf 1641458651) (.leaf 1608950223)) (.branch 51 (.leaf 1577254371) (.leaf 1546343044)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1516189461) (.leaf 1486768048)) (.branch 55 (.leaf 1458054373) (.leaf 1430025084))) (.branch 58 (.branch 57 (.leaf 1402657855) (.leaf 1375931330)) (.branch 59 (.leaf 1349825074) (.leaf 1324319525))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1299395950) (.branch 62 (.leaf 1275036401) (.leaf 1251223678))) (.branch 65 (.branch 64 (.leaf 1227941288) (.leaf 1205173412)) (.branch 66 (.leaf 1182904871) (.leaf 1161121093)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1139808084) (.leaf 1118952403)) (.branch 70 (.leaf 1098541127) (.leaf 1078561834))) (.branch 73 (.branch 72 (.leaf 1059002577) (.leaf 1039851857)) (.branch 74 (.leaf 1021098608) (.leaf 1002732172))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 984742282) (.branch 77 (.leaf 967119044) (.leaf 949852920))) (.branch 80 (.branch 79 (.leaf 932934708) (.leaf 916355533)) (.branch 81 (.leaf 900106828) (.leaf 884180319)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 868568018) (.leaf 853262203)) (.branch 85 (.leaf 838255412) (.leaf 823540428))) (.branch 88 (.branch 87 (.leaf 809110271) (.leaf 794958187)) (.branch 89 (.leaf 781077636) (.leaf 767462288)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 754106010) (.branch 92 (.leaf 741002858) (.leaf 728147073))) (.branch 95 (.branch 94 (.leaf 715533069) (.leaf 703155429)) (.branch 96 (.leaf 691008895) (.leaf 679088367)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 667388890) (.leaf 655905655)) (.branch 100 (.leaf 644633989) (.leaf 633569349))) (.branch 103 (.branch 102 (.leaf 622707323) (.leaf 612043618)) (.branch 104 (.leaf 601574060) (.leaf 591294588))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 581201250) (.leaf 571290199)) (.branch 108 (.leaf 561557690) (.leaf 552000076))) (.branch 111 (.branch 110 (.leaf 542613803) (.leaf 533395410)) (.branch 112 (.leaf 524341522) (.leaf 515448849)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 506714186) (.leaf 498134403)) (.branch 116 (.leaf 489706449) (.leaf 481427347))) (.branch 119 (.branch 118 (.leaf 473294191) (.leaf 465304145)) (.branch 120 (.leaf 457454441) (.leaf 449742373)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hcontinuation : (generalMeanRows 155).q*(generalMeanRows 155).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5262276832) (.branch 2 (.leaf 5090846698) (.leaf 4927223785))) (.branch 5 (.branch 4 (.leaf 4770948485) (.leaf 4621594206)) (.branch 6 (.leaf 4478764491) (.leaf 4342090442)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4211228418) (.leaf 4085857958)) (.branch 10 (.leaf 3965679922) (.leaf 3850414802))) (.branch 13 (.branch 12 (.leaf 3739801196) (.leaf 3633594431)) (.branch 14 (.leaf 3531565299) (.leaf 3433498918))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3339193680) (.branch 17 (.leaf 3248460303) (.leaf 3161120951))) (.branch 20 (.branch 19 (.leaf 3077008436) (.leaf 2995965477)) (.branch 21 (.leaf 2917844026) (.leaf 2842504643)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2769815921) (.leaf 2699653952)) (.branch 25 (.leaf 2631901841) (.leaf 2566449247))) (.branch 28 (.branch 27 (.leaf 2503191965) (.leaf 2442031534)) (.branch 29 (.leaf 2382874878) (.leaf 2325633967)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2270225503) (.branch 32 (.leaf 2216570635) (.leaf 2164594682))) (.branch 35 (.branch 34 (.leaf 2114226884) (.leaf 2065400167)) (.branch 36 (.leaf 2018050922) (.leaf 1972118801)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1927546524) (.leaf 1884279704)) (.branch 40 (.leaf 1842266674) (.leaf 1801458336))) (.branch 43 (.branch 42 (.leaf 1761808011) (.leaf 1723271302)) (.branch 44 (.leaf 1685805966) (.leaf 1649371794))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1613930496) (.branch 47 (.leaf 1579445596) (.leaf 1545882330))) (.branch 50 (.branch 49 (.leaf 1513207558) (.leaf 1481389668)) (.branch 51 (.leaf 1450398499) (.leaf 1420205264)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1390782469) (.leaf 1362103854)) (.branch 55 (.leaf 1334144321) (.leaf 1306879877))) (.branch 58 (.branch 57 (.leaf 1280287574) (.leaf 1254345457)) (.branch 59 (.leaf 1229032509) (.leaf 1204328609))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1180214480) (.branch 62 (.leaf 1156671652) (.leaf 1133682416))) (.branch 65 (.branch 64 (.leaf 1111229791) (.leaf 1089297484)) (.branch 66 (.leaf 1067869858) (.leaf 1046931901)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1026469190) (.leaf 1006467870)) (.branch 70 (.leaf 986914621) (.leaf 967796636))) (.branch 73 (.branch 72 (.leaf 949101593) (.leaf 930817636)) (.branch 74 (.leaf 912933350) (.leaf 895437743))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 878320223) (.branch 77 (.leaf 861570585) (.leaf 845178986))) (.branch 80 (.branch 79 (.leaf 829135937) (.leaf 813432280)) (.branch 81 (.leaf 798059177) (.leaf 783008093)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 768270788) (.leaf 753839298)) (.branch 85 (.leaf 739705926) (.leaf 725863230))) (.branch 88 (.branch 87 (.leaf 712304013) (.leaf 699021311)) (.branch 89 (.leaf 686008384) (.leaf 673258709)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 660765964) (.branch 92 (.leaf 648524030) (.leaf 636526972))) (.branch 95 (.branch 94 (.leaf 624769042) (.leaf 613244661)) (.branch 96 (.leaf 601948422) (.leaf 590875076)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 580019529) (.leaf 569376838)) (.branch 100 (.leaf 558942201) (.leaf 548710952))) (.branch 103 (.branch 102 (.leaf 538678561) (.leaf 528840622)) (.branch 104 (.leaf 519192854) (.leaf 509731093))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 500451289) (.leaf 491349502)) (.branch 108 (.leaf 482421898) (.leaf 473664745))) (.branch 111 (.branch 110 (.leaf 465074409) (.leaf 456647352)) (.branch 112 (.leaf 448380127) (.leaf 440269377)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 432311830) (.leaf 424504296)) (.branch 116 (.leaf 416843667) (.leaf 409326910))) (.branch 119 (.branch 118 (.leaf 401951070) (.leaf 394713262)) (.branch 120 (.leaf 387610673) (.leaf 380640558)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 156).q*(generalMeanRows 156).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    have hcontinuation : (generalMeanRows 156).q*(generalMeanRows 156).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5245559431) (.branch 2 (.leaf 5071951810) (.leaf 4906210213))) (.branch 5 (.branch 4 (.leaf 4747876892) (.leaf 4596526743)) (.branch 6 (.leaf 4451764465) (.leaf 4313222012)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4180556316) (.leaf 4053447246)) (.branch 10 (.leaf 3931595763) (.leaf 3814722261))) (.branch 13 (.branch 12 (.leaf 3702565062) (.leaf 3594879054)) (.branch 14 (.leaf 3491434447) (.leaf 3392015649))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296420234) (.branch 17 (.leaf 3204458001) (.leaf 3115950111))) (.branch 20 (.branch 19 (.leaf 3030728297) (.leaf 2948634138)) (.branch 21 (.leaf 2869518392) (.leaf 2793240380)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2719667417) (.leaf 2648674289)) (.branch 25 (.leaf 2580142771) (.leaf 2513961177))) (.branch 28 (.branch 27 (.leaf 2450023941) (.leaf 2388231239)) (.branch 29 (.leaf 2328488626) (.leaf 2270706705)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2214800817) (.branch 32 (.leaf 2160690757) (.leaf 2108300501))) (.branch 35 (.branch 34 (.leaf 2057557961) (.leaf 2008394749)) (.branch 36 (.leaf 1960745960) (.leaf 1914549968)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1869748239) (.leaf 1826285150)) (.branch 40 (.leaf 1784107826) (.leaf 1743165979))) (.branch 43 (.branch 42 (.leaf 1703411770) (.leaf 1664799663)) (.branch 44 (.leaf 1627286307) (.leaf 1590830405))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1555392610) (.branch 47 (.leaf 1520935414) (.leaf 1487423048))) (.branch 50 (.branch 49 (.leaf 1454821393) (.leaf 1423097886)) (.branch 51 (.leaf 1392221441) (.leaf 1362162370)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1332892308) (.leaf 1304384147)) (.branch 55 (.leaf 1276611968) (.leaf 1249550980))) (.branch 58 (.branch 57 (.leaf 1223177465) (.leaf 1197468717)) (.branch 59 (.leaf 1172402999) (.leaf 1147959487))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1124118229) (.branch 62 (.leaf 1100860098) (.leaf 1078166754))) (.branch 65 (.branch 64 (.leaf 1056020603) (.leaf 1034404763)) (.branch 66 (.leaf 1013303027) (.leaf 992699832)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 972580226) (.leaf 952929843)) (.branch 70 (.leaf 933734870) (.leaf 914982024))) (.branch 73 (.branch 72 (.leaf 896658527) (.leaf 878752082)) (.branch 74 (.leaf 861250851) (.leaf 844143434))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 827418846) (.branch 77 (.leaf 811066505) (.leaf 795076208))) (.branch 80 (.branch 79 (.leaf 779438114) (.leaf 764142733)) (.branch 81 (.leaf 749180905) (.leaf 734543788)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 720222844) (.leaf 706209827)) (.branch 85 (.leaf 692496767) (.leaf 679075962))) (.branch 88 (.branch 87 (.leaf 665939966) (.leaf 653081574)) (.branch 89 (.leaf 640493819) (.leaf 628169956)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 616103457) (.branch 92 (.leaf 604288000) (.leaf 592717460))) (.branch 95 (.branch 94 (.leaf 581385904) (.leaf 570287581)) (.branch 96 (.leaf 559416916) (.leaf 548768501)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 538337091) (.leaf 528117598)) (.branch 100 (.leaf 518105081) (.leaf 508294747))) (.branch 103 (.branch 102 (.leaf 498681938) (.leaf 489262131)) (.branch 104 (.leaf 480030933) (.leaf 470984073))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 462117399) (.leaf 453426877)) (.branch 108 (.leaf 444908580) (.leaf 436558692))) (.branch 111 (.branch 110 (.leaf 428373498) (.leaf 420349382)) (.branch 112 (.leaf 412482826) (.leaf 404770405)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 397208782) (.leaf 389794707)) (.branch 116 (.leaf 382525017) (.leaf 375396626))) (.branch 119 (.branch 118 (.leaf 368406529) (.leaf 361551796)) (.branch 120 (.leaf 354829570) (.leaf 348237066)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 157).q*(generalMeanRows 157).c/2-2 = (289/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable093.value]
    have hcontinuation : (generalMeanRows 157).q*(generalMeanRows 157).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4960452223) (.branch 2 (.leaf 4786176522) (.leaf 4619908584))) (.branch 5 (.branch 4 (.leaf 4461184051) (.leaf 4309571574)) (.branch 6 (.leaf 4164669930) (.leaf 4026105457)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3893529752) (.leaf 3766617606)) (.branch 10 (.leaf 3645065143) (.leaf 3528588143))) (.branch 13 (.branch 12 (.leaf 3416920521) (.leaf 3309812953)) (.branch 14 (.leaf 3207031619) (.leaf 3108357069))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3013583176) (.branch 17 (.leaf 2922516191) (.leaf 2834973870))) (.branch 20 (.branch 19 (.leaf 2750784676) (.leaf 2669787044)) (.branch 21 (.leaf 2591828709) (.leaf 2516766083)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2444463685) (.leaf 2374793606)) (.branch 25 (.leaf 2307635025) (.leaf 2242873754))) (.branch 28 (.branch 27 (.leaf 2180401820) (.leaf 2120117074)) (.branch 29 (.leaf 2061922830) (.leaf 2005727529)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1951444431) (.branch 32 (.leaf 1898991316) (.leaf 1848290222))) (.branch 35 (.branch 34 (.leaf 1799267187) (.leaf 1751852015)) (.branch 36 (.leaf 1705978056) (.leaf 1661582002)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1618603692) (.leaf 1576985934)) (.branch 40 (.leaf 1536674338) (.leaf 1497617156))) (.branch 43 (.branch 42 (.leaf 1459765136) (.leaf 1423071383)) (.branch 44 (.leaf 1387491229) (.leaf 1352982111))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1319503458) (.branch 47 (.leaf 1287016581) (.leaf 1255484574))) (.branch 50 (.branch 49 (.leaf 1224872219) (.leaf 1195145894)) (.branch 51 (.leaf 1166273492) (.leaf 1138224341)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1110969129) (.leaf 1084479832)) (.branch 55 (.leaf 1058729653) (.leaf 1033692952))) (.branch 58 (.branch 57 (.leaf 1009345194) (.leaf 985662890)) (.branch 59 (.leaf 962623546) (.leaf 940205611))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 918388432) (.branch 62 (.leaf 897152212) (.leaf 876477965))) (.branch 65 (.branch 64 (.leaf 856347477) (.leaf 836743269)) (.branch 66 (.leaf 817648563) (.leaf 799047247)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 780923845) (.leaf 763263486)) (.branch 70 (.leaf 746051874) (.leaf 729275264))) (.branch 73 (.branch 72 (.leaf 712920437) (.leaf 696974672)) (.branch 74 (.leaf 681425728) (.leaf 666261818))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 651471591) (.branch 77 (.leaf 637044113) (.leaf 622968846))) (.branch 80 (.branch 79 (.leaf 609235632) (.leaf 595834678)) (.branch 81 (.leaf 582756536) (.leaf 569992092)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 557532549) (.leaf 545369416)) (.branch 85 (.leaf 533494492) (.leaf 521899857))) (.branch 88 (.branch 87 (.leaf 510577856) (.leaf 499521094)) (.branch 89 (.leaf 488722419) (.leaf 478174916)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 467871897) (.branch 92 (.leaf 457806889) (.leaf 447973631))) (.branch 95 (.branch 94 (.leaf 438366060) (.leaf 428978304)) (.branch 96 (.leaf 419804678) (.leaf 410839674)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 402077954) (.leaf 393514345)) (.branch 100 (.leaf 385143833) (.leaf 376961552))) (.branch 103 (.branch 102 (.leaf 368962787) (.leaf 361142961)) (.branch 104 (.leaf 353497634) (.leaf 346022495))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 338713362) (.leaf 331566170)) (.branch 108 (.leaf 324576976) (.leaf 317741946))) (.branch 111 (.branch 110 (.leaf 311057357) (.leaf 304519590)) (.branch 112 (.leaf 298125129) (.leaf 291870555)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285752542) (.leaf 279767859)) (.branch 116 (.leaf 273913361) (.leaf 268185988))) (.branch 119 (.branch 118 (.leaf 262582765) (.leaf 257100794)) (.branch 120 (.leaf 251737257) (.leaf 246489408)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 158).q*(generalMeanRows 158).c/2-2 = (13/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable042.value]
    have hcontinuation : (generalMeanRows 158).q*(generalMeanRows 158).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5056512760) (.branch 2 (.leaf 4883866020) (.leaf 4719158736))) (.branch 5 (.branch 4 (.leaf 4561925099) (.leaf 4411732675)) (.branch 6 (.leaf 4268179493) (.leaf 4130891444)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3999519949) (.leaf 3873739870)) (.branch 10 (.leaf 3753247622) (.leaf 3637759471))) (.branch 13 (.branch 12 (.leaf 3527009998) (.leaf 3420750696)) (.branch 14 (.leaf 3318748701) (.leaf 3220785641))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3126656574) (.branch 17 (.leaf 3036169023) (.leaf 2949142100))) (.branch 20 (.branch 19 (.leaf 2865405687) (.leaf 2784799698)) (.branch 21 (.leaf 2707173392) (.leaf 2632384743)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2560299860) (.leaf 2490792450)) (.branch 25 (.leaf 2423743323) (.leaf 2359039928))) (.branch 28 (.branch 27 (.leaf 2296575938) (.leaf 2236250846)) (.branch 29 (.leaf 2177969604) (.leaf 2121642284)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2067183761) (.branch 32 (.leaf 2014513418) (.leaf 1963554875))) (.branch 35 (.branch 34 (.leaf 1914235733) (.leaf 1866487333)) (.branch 36 (.leaf 1820244541) (.leaf 1775445537)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1732031618) (.leaf 1689947025)) (.branch 40 (.leaf 1649138769) (.leaf 1609556470))) (.branch 43 (.branch 42 (.leaf 1571152215) (.leaf 1533880417)) (.branch 44 (.leaf 1497697680) (.leaf 1462562685))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1428436067) (.branch 47 (.leaf 1395280314) (.leaf 1363059664))) (.branch 50 (.branch 49 (.leaf 1331740008) (.leaf 1301288802)) (.branch 51 (.leaf 1271674987) (.leaf 1242868902)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1214842218) (.leaf 1187567863)) (.branch 55 (.leaf 1161019959) (.leaf 1135173758))) (.branch 58 (.branch 57 (.leaf 1110005584) (.leaf 1085492780)) (.branch 59 (.leaf 1061613653) (.leaf 1038347427))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1015674199) (.branch 62 (.leaf 993574888) (.leaf 972031203))) (.branch 65 (.branch 64 (.leaf 951025599) (.leaf 930541240)) (.branch 66 (.leaf 910561966) (.leaf 891072260)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 872057218) (.leaf 853502516)) (.branch 70 (.leaf 835394387) (.leaf 817719592))) (.branch 73 (.branch 72 (.leaf 800465394) (.leaf 783619540)) (.branch 74 (.leaf 767170231) (.leaf 751106107))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 735416225) (.branch 77 (.leaf 720090041) (.leaf 705117388))) (.branch 80 (.branch 79 (.leaf 690488465) (.leaf 676193816)) (.branch 81 (.leaf 662224319) (.leaf 648571167)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 635225857) (.leaf 622180176)) (.branch 85 (.leaf 609426190) (.leaf 596956230))) (.branch 88 (.branch 87 (.leaf 584762881) (.leaf 572838973)) (.branch 89 (.leaf 561177572) (.leaf 549771964)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 538615654) (.branch 92 (.leaf 527702350) (.leaf 517025962))) (.branch 95 (.branch 94 (.leaf 506580587) (.leaf 496360507)) (.branch 96 (.leaf 486360176) (.leaf 476574221)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 466997427) (.leaf 457624739)) (.branch 100 (.leaf 448451248) (.leaf 439472192))) (.branch 103 (.branch 102 (.leaf 430682947) (.leaf 422079022)) (.branch 104 (.leaf 413656057) (.leaf 405409814))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 397336175) (.leaf 389431139)) (.branch 108 (.leaf 381690814) (.leaf 374111416))) (.branch 111 (.branch 110 (.leaf 366689267) (.leaf 359420785)) (.branch 112 (.leaf 352302488) (.leaf 345330984)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 338502975) (.leaf 331815248)) (.branch 116 (.leaf 325264674) (.leaf 318848205))) (.branch 119 (.branch 118 (.leaf 312562873) (.leaf 306405788)) (.branch 120 (.leaf 300374129) (.leaf 294465151)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 159).q*(generalMeanRows 159).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 159).q*(generalMeanRows 159).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5294549380) (.branch 2 (.leaf 5122104783) (.leaf 4957545098))) (.branch 5 (.branch 4 (.leaf 4800403703) (.leaf 4650247606)) (.branch 6 (.leaf 4506674511) (.leaf 4369310194)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4237806152) (.leaf 4111837493)) (.branch 10 (.leaf 3991101028) (.leaf 3875313560))) (.branch 13 (.branch 12 (.leaf 3764210325) (.leaf 3657543582)) (.branch 14 (.leaf 3555081328) (.leaf 3456606133))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3361914075) (.branch 17 (.leaf 3270813759) (.leaf 3183125434))) (.branch 20 (.branch 19 (.leaf 3098680164) (.leaf 3017319088)) (.branch 21 (.leaf 2938892719) (.leaf 2863260314)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2790289285) (.leaf 2719854657)) (.branch 25 (.leaf 2651838566) (.leaf 2586129802))) (.branch 28 (.branch 27 (.leaf 2522623371) (.leaf 2461220107)) (.branch 29 (.leaf 2401826294) (.leaf 2344353332)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2288717412) (.branch 32 (.leaf 2234839223) (.leaf 2182643678))) (.branch 35 (.branch 34 (.leaf 2132059654) (.leaf 2083019752)) (.branch 36 (.leaf 2035460080) (.leaf 1989320037)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1944542123) (.leaf 1901071756)) (.branch 40 (.leaf 1858857103) (.leaf 1817848920))) (.branch 43 (.branch 42 (.leaf 1778000401) (.leaf 1739267044)) (.branch 44 (.leaf 1701606514) (.leaf 1664978528))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1629344731) (.branch 47 (.leaf 1594668599) (.leaf 1560915326))) (.branch 50 (.branch 49 (.leaf 1528051742) (.leaf 1496046212)) (.branch 51 (.leaf 1464868561) (.leaf 1434489991)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1404883005) (.leaf 1376021346)) (.branch 55 (.leaf 1347879920) (.leaf 1320434743))) (.branch 58 (.branch 57 (.leaf 1293662880) (.leaf 1267542389)) (.branch 59 (.leaf 1242052271) (.leaf 1217172422))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1192883586) (.branch 62 (.leaf 1169167311) (.leaf 1146005911))) (.branch 65 (.branch 64 (.leaf 1123382425) (.leaf 1101280584)) (.branch 66 (.leaf 1079684771) (.leaf 1058579994)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1037951853) (.leaf 1017786514)) (.branch 70 (.leaf 998070676) (.leaf 978791552))) (.branch 73 (.branch 72 (.leaf 959936837) (.leaf 941494694)) (.branch 74 (.leaf 923453725) (.leaf 905802952))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 888531800) (.branch 77 (.leaf 871630075) (.leaf 855087949))) (.branch 80 (.branch 79 (.leaf 838895943) (.leaf 823044910)) (.branch 81 (.leaf 807526021) (.leaf 792330751)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 777450865) (.leaf 762878405)) (.branch 85 (.leaf 748605681) (.leaf 734625254))) (.branch 88 (.branch 87 (.leaf 720929930) (.leaf 707512747)) (.branch 89 (.leaf 694366967) (.leaf 681486064)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 668863720) (.branch 92 (.leaf 656493811) (.leaf 644370401))) (.branch 95 (.branch 94 (.leaf 632487736) (.leaf 620840236)) (.branch 96 (.leaf 609422488) (.leaf 598229237)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 587255384) (.leaf 576495977)) (.branch 100 (.leaf 565946207) (.leaf 555601402))) (.branch 103 (.branch 102 (.leaf 545457019) (.leaf 535508646)) (.branch 104 (.leaf 525751991) (.leaf 516182879))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 506797251) (.leaf 497591153)) (.branch 108 (.leaf 488560742) (.leaf 479702272))) (.branch 111 (.branch 110 (.leaf 471012098) (.leaf 462486668)) (.branch 112 (.leaf 454122524) (.leaf 445916293)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 437864690) (.leaf 429964513)) (.branch 116 (.leaf 422212638) (.leaf 414606020))) (.branch 119 (.branch 118 (.leaf 407141687) (.leaf 399816742)) (.branch 120 (.leaf 392628355) (.leaf 385573766)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 160).q*(generalMeanRows 160).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    have hcontinuation : (generalMeanRows 160).q*(generalMeanRows 160).cutoff/2-2 = (1774/805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable094.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5330184063) (.branch 2 (.leaf 5156578837) (.leaf 4990911592))) (.branch 5 (.branch 4 (.leaf 4832712565) (.leaf 4681545850)) (.branch 6 (.leaf 4537006444) (.leaf 4398717604)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4266328481) (.leaf 4139511996)) (.branch 10 (.leaf 4017962921) (.leaf 3901396152))) (.branch 13 (.branch 12 (.leaf 3789545143) (.leaf 3682160484)) (.branch 14 (.leaf 3579008613) (.leaf 3479870637))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3384541258) (.branch 17 (.leaf 3292827797) (.leaf 3204549290))) (.branch 20 (.branch 19 (.leaf 3119535666) (.leaf 3037626993)) (.branch 21 (.leaf 2958672780) (.leaf 2882531335)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2809069179) (.leaf 2738160494)) (.branch 25 (.leaf 2669686625) (.leaf 2603535611))) (.branch 28 (.branch 27 (.leaf 2539601754) (.leaf 2477785218)) (.branch 29 (.leaf 2417991658) (.leaf 2360131877)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2304121502) (.branch 32 (.leaf 2249880690) (.leaf 2197333846))) (.branch 35 (.branch 34 (.leaf 2146409368) (.leaf 2097039406)) (.branch 36 (.leaf 2049159636) (.leaf 2002709049)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1957629760) (.leaf 1913866818)) (.branch 40 (.leaf 1871368042) (.leaf 1830083855))) (.branch 43 (.branch 42 (.leaf 1789967138) (.leaf 1750973088)) (.branch 44 (.leaf 1713059087) (.leaf 1676184577))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1640310949) (.branch 47 (.leaf 1605401431) (.leaf 1571420984))) (.branch 50 (.branch 49 (.leaf 1538336213) (.leaf 1506115272)) (.branch 51 (.leaf 1474727781) (.leaf 1444144749)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1414338496) (.leaf 1385282584)) (.branch 55 (.leaf 1356951754) (.leaf 1329321859))) (.branch 58 (.branch 57 (.leaf 1302369809) (.leaf 1276073515)) (.branch 59 (.leaf 1250411838) (.leaf 1225364536))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1200912225) (.branch 62 (.leaf 1177036329) (.leaf 1153719043))) (.branch 65 (.branch 64 (.leaf 1130943291) (.leaf 1108692694)) (.branch 66 (.leaf 1086951531) (.leaf 1065704710)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1044937733) (.leaf 1024636672)) (.branch 70 (.leaf 1004788138) (.leaf 985379256))) (.branch 73 (.branch 72 (.leaf 966397641) (.leaf 947831374)) (.branch 74 (.leaf 929668981) (.leaf 911899410))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 894512016) (.branch 77 (.leaf 877496534) (.leaf 860843073))) (.branch 80 (.branch 79 (.leaf 844542087) (.leaf 828584370)) (.branch 81 (.leaf 812961032) (.leaf 797663491)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 782683456) (.leaf 768012918)) (.branch 85 (.leaf 753644132) (.leaf 739569610))) (.branch 88 (.branch 87 (.leaf 725782110) (.leaf 712274624)) (.branch 89 (.leaf 699040367) (.leaf 686072770)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 673365472) (.branch 92 (.leaf 660912307) (.leaf 648707301))) (.branch 95 (.branch 94 (.leaf 636744661) (.leaf 625018769)) (.branch 96 (.leaf 613524174) (.leaf 602255587)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 591207875) (.leaf 580376053)) (.branch 100 (.leaf 569755278) (.leaf 559340847))) (.branch 103 (.branch 102 (.leaf 549128189) (.leaf 539112859)) (.branch 104 (.leaf 529290537) (.leaf 519657021))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 510208222) (.leaf 500940164)) (.branch 108 (.leaf 491848974) (.leaf 482930883))) (.branch 111 (.branch 110 (.leaf 474182220) (.leaf 465599410)) (.branch 112 (.leaf 457178971) (.leaf 448917509)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 440811715) (.leaf 432858366)) (.branch 116 (.leaf 425054318) (.leaf 417396504))) (.branch 119 (.branch 118 (.leaf 409881933) (.leaf 402507687)) (.branch 120 (.leaf 395270919) (.leaf 388168850)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 161).q*(generalMeanRows 161).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    have hcontinuation : (generalMeanRows 161).q*(generalMeanRows 161).cutoff/2-2 = (1774/805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable094.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5091085157) (.branch 2 (.leaf 4917257997) (.leaf 4751424575))) (.branch 5 (.branch 4 (.leaf 4593115900) (.leaf 4441896581)) (.branch 6 (.leaf 4297361897) (.leaf 4159135181)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4026865473) (.leaf 3900225410)) (.branch 10 (.leaf 3778909332) (.leaf 3662631566))) (.branch 13 (.branch 12 (.leaf 3551124877) (.leaf 3444139058)) (.branch 14 (.leaf 3341439655) (.leaf 3242806802))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3148034155) (.branch 17 (.leaf 3056927923) (.leaf 2969305979))) (.branch 20 (.branch 19 (.leaf 2884997043) (.leaf 2803839935)) (.branch 21 (.leaf 2725682882) (.leaf 2650382888)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2577805146) (.leaf 2507822500)) (.branch 25 (.leaf 2440314944) (.leaf 2375169160))) (.branch 28 (.branch 27 (.leaf 2312278091) (.leaf 2251540543)) (.branch 29 (.leaf 2192860821) (.leaf 2136148380)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2081317513) (.branch 32 (.leaf 2028287053) (.leaf 1976980096))) (.branch 35 (.branch 34 (.leaf 1927323748) (.leaf 1879248883)) (.branch 36 (.leaf 1832689920) (.leaf 1787584616)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1743873867) (.leaf 1701501534)) (.branch 40 (.leaf 1660414263) (.leaf 1620561332))) (.branch 43 (.branch 42 (.leaf 1581894500) (.leaf 1544367867)) (.branch 44 (.leaf 1507937741) (.leaf 1472562521))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1438202572) (.branch 47 (.leaf 1404820127) (.leaf 1372379178))) (.branch 50 (.branch 49 (.leaf 1340845382) (.leaf 1310185976)) (.branch 51 (.leaf 1280369685) (.leaf 1251366647)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1223148339) (.leaf 1195687504)) (.branch 55 (.leaf 1168958087) (.leaf 1142935170))) (.branch 58 (.branch 57 (.leaf 1117594916) (.leaf 1092914513)) (.branch 59 (.leaf 1068872119) (.leaf 1045446818))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1022618568) (.branch 62 (.leaf 1000368160) (.leaf 978677177))) (.branch 65 (.branch 64 (.leaf 957527953) (.leaf 936903538)) (.branch 66 (.leaf 916787662) (.leaf 897164701)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 878019649) (.leaf 859338085)) (.branch 70 (.leaf 841106147) (.leaf 823310505))) (.branch 73 (.branch 72 (.leaf 805938337) (.leaf 788977304)) (.branch 74 (.leaf 772415528) (.leaf 756241571))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 740444414) (.branch 77 (.leaf 725013442) (.leaf 709938418))) (.branch 80 (.branch 79 (.leaf 695209474) (.leaf 680817090)) (.branch 81 (.leaf 666752080) (.leaf 653005579)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 639569024) (.leaf 626434147)) (.branch 85 (.leaf 613592960) (.leaf 601037740))) (.branch 88 (.branch 87 (.leaf 588761022) (.leaf 576755589)) (.branch 89 (.leaf 565014456) (.leaf 553530866)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 542298277) (.branch 92 (.leaf 531310358) (.leaf 520560973))) (.branch 95 (.branch 94 (.leaf 510044181) (.leaf 499754223)) (.branch 96 (.leaf 489685519) (.leaf 479832655)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 470190383) (.leaf 460753611)) (.branch 100 (.leaf 451517399) (.leaf 442476952))) (.branch 103 (.branch 102 (.leaf 433627613) (.leaf 424964862)) (.branch 104 (.leaf 416484307) (.leaf 408181683))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 400052843) (.leaf 392093758)) (.branch 108 (.leaf 384300511) (.leaf 376669292))) (.branch 111 (.branch 110 (.leaf 369196395) (.leaf 361878217)) (.branch 112 (.leaf 354711251) (.leaf 347692082)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 340817389) (.leaf 334083936)) (.branch 116 (.leaf 327488574) (.leaf 321028234))) (.branch 119 (.branch 118 (.leaf 314699929) (.leaf 308500746)) (.branch 120 (.leaf 302427847) (.leaf 296478468)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 162).q*(generalMeanRows 162).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 162).q*(generalMeanRows 162).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5125893932) (.branch 2 (.leaf 4950878281) (.leaf 4783911023))) (.branch 5 (.branch 4 (.leaf 4624519960) (.leaf 4472266723)) (.branch 6 (.leaf 4326743826) (.leaf 4187572027)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4054397964) (.leaf 3926892038)) (.branch 10 (.leaf 3804746497) (.leaf 3687673716))) (.branch 13 (.branch 12 (.leaf 3575404633) (.leaf 3467687331)) (.branch 14 (.leaf 3364285752) (.leaf 3264978526))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3169557899) (.branch 17 (.leaf 3077828755) (.leaf 2989607723))) (.branch 20 (.branch 19 (.leaf 2904722350) (.leaf 2823010354)) (.branch 21 (.leaf 2744318925) (.leaf 2668504090)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2595430120) (.leaf 2524968988)) (.branch 25 (.leaf 2456999869) (.leaf 2391408670))) (.branch 28 (.branch 27 (.leaf 2328087602) (.leaf 2266934780)) (.branch 29 (.leaf 2207853852) (.leaf 2150753657)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2095547900) (.branch 32 (.leaf 2042154860) (.leaf 1990497107))) (.branch 35 (.branch 34 (.leaf 1940501249) (.leaf 1892097687)) (.branch 36 (.leaf 1845220391) (.leaf 1799806692)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1755797085) (.leaf 1713135043)) (.branch 40 (.leaf 1671766850) (.leaf 1631641436))) (.branch 43 (.branch 42 (.leaf 1592710231) (.leaf 1554927021)) (.branch 44 (.leaf 1518247816) (.leaf 1482630727))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1448035853) (.branch 47 (.leaf 1414425165) (.leaf 1381762411))) (.branch 50 (.branch 49 (.leaf 1350013013) (.leaf 1319143982)) (.branch 51 (.leaf 1289123830) (.leaf 1259922493)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1231511251) (.leaf 1203862661)) (.branch 55 (.leaf 1176950489) (.leaf 1150749648))) (.branch 58 (.branch 57 (.leaf 1125236138) (.leaf 1100386990)) (.branch 59 (.leaf 1076180213) (.leaf 1052594749))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1029610417) (.branch 62 (.leaf 1007207879) (.leaf 985368590))) (.branch 65 (.branch 64 (.leaf 964074764) (.leaf 943309336)) (.branch 66 (.leaf 923055924) (.leaf 903298797)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 884022846) (.leaf 865213553)) (.branch 70 (.leaf 846856959) (.leaf 828939645))) (.branch 73 (.branch 72 (.leaf 811448700) (.leaf 794371701)) (.branch 74 (.leaf 777696689) (.leaf 761412147))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 745506982) (.branch 77 (.leaf 729970505) (.leaf 714792410))) (.branch 80 (.branch 79 (.leaf 699962761) (.leaf 685471973)) (.branch 81 (.leaf 671310799) (.leaf 657470310)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643941886) (.leaf 630717204)) (.branch 85 (.leaf 617788218) (.leaf 605147156))) (.branch 88 (.branch 87 (.leaf 592786500) (.leaf 580698983)) (.branch 89 (.leaf 568877574) (.leaf 557315468)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 546006080) (.branch 92 (.leaf 534943034) (.leaf 524120153))) (.branch 95 (.branch 94 (.leaf 513531456) (.leaf 503171144)) (.branch 96 (.leaf 493033597) (.leaf 483113367)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 473405169) (.leaf 463903876)) (.branch 100 (.leaf 454604515) (.leaf 445502256))) (.branch 103 (.branch 102 (.leaf 436592412) (.leaf 427870432)) (.branch 104 (.leaf 419331894) (.leaf 410972503))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402788085) (.leaf 394774582)) (.branch 108 (.leaf 386928051) (.leaf 379244655))) (.branch 111 (.branch 110 (.leaf 371720665) (.leaf 364352452)) (.branch 112 (.leaf 357136483) (.leaf 350069323)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 343147626) (.leaf 336368135)) (.branch 116 (.leaf 329727679) (.leaf 323223169))) (.branch 119 (.branch 118 (.leaf 316851596) (.leaf 310610028)) (.branch 120 (.leaf 304495608) (.leaf 298505551)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 163).q*(generalMeanRows 163).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 163).q*(generalMeanRows 163).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5096111890) (.branch 2 (.leaf 4922157255) (.leaf 4756169879))) (.branch 5 (.branch 4 (.leaf 4597684708) (.leaf 4446269900)) (.branch 6 (.leaf 4301523931) (.leaf 4163073008)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4030568748) (.leaf 3903686103)) (.branch 10 (.leaf 3782121480) (.leaf 3665591054))) (.branch 13 (.branch 12 (.leaf 3553829232) (.leaf 3446587270)) (.branch 14 (.leaf 3343632007) (.leaf 3244744716))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3149720057) (.branch 17 (.leaf 3058365114) (.leaf 2970498523))) (.branch 20 (.branch 19 (.leaf 2885949663) (.leaf 2804557918)) (.branch 21 (.leaf 2726171996) (.leaf 2650649303)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2577855366) (.leaf 2507663300)) (.branch 25 (.leaf 2439953312) (.leaf 2374612248))) (.branch 28 (.branch 27 (.leaf 2311533171) (.leaf 2250614964)) (.branch 29 (.leaf 2191761971) (.leaf 2134883659)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2079894298) (.branch 32 (.leaf 2026712677) (.leaf 1975261825))) (.branch 35 (.branch 34 (.leaf 1925468759) (.leaf 1877264249)) (.branch 36 (.leaf 1830582594) (.leaf 1785361418)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1741541476) (.leaf 1699066473)) (.branch 40 (.leaf 1657882898) (.leaf 1617939861))) (.branch 43 (.branch 42 (.leaf 1579188950) (.leaf 1541584089)) (.branch 44 (.leaf 1505081409) (.leaf 1469639127))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1435217428) (.branch 47 (.leaf 1401778364) (.leaf 1369285744))) (.branch 50 (.branch 49 (.leaf 1337705047) (.leaf 1307003329)) (.branch 51 (.leaf 1277149137) (.leaf 1248112437)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1219864532) (.leaf 1192377996)) (.branch 55 (.leaf 1165626606) (.leaf 1139585284))) (.branch 58 (.branch 57 (.leaf 1114230032) (.leaf 1089537881)) (.branch 59 (.leaf 1065486841) (.leaf 1042055845))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1019224708) (.branch 62 (.leaf 996974081) (.leaf 975285412))) (.branch 65 (.branch 64 (.leaf 954140904) (.leaf 933523478)) (.branch 66 (.leaf 913416741) (.leaf 893804952)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 874672987) (.leaf 856006315)) (.branch 70 (.leaf 837790967) (.leaf 820013510))) (.branch 73 (.branch 72 (.leaf 802661022) (.leaf 785721068)) (.branch 74 (.leaf 769181679) (.leaf 753031328))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 737258913) (.branch 77 (.leaf 721853735) (.leaf 706805481))) (.branch 80 (.branch 79 (.leaf 692104208) (.leaf 677740324)) (.branch 81 (.leaf 663704576) (.leaf 649988032)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 636582067) (.leaf 623478354)) (.branch 85 (.leaf 610668848) (.leaf 598145771))) (.branch 88 (.branch 87 (.leaf 585901609) (.leaf 573929093)) (.branch 89 (.leaf 562221192) (.leaf 550771106)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 539572250) (.branch 92 (.leaf 528618252) (.leaf 517902939))) (.branch 95 (.branch 94 (.leaf 507420335) (.leaf 497164646)) (.branch 96 (.leaf 487130259) (.leaf 477311732)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 467703786) (.leaf 458301304)) (.branch 100 (.leaf 449099319) (.leaf 440093011))) (.branch 103 (.branch 102 (.leaf 431277703) (.leaf 422648853)) (.branch 104 (.leaf 414202049) (.leaf 405933007))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 397837564) (.leaf 389911674)) (.branch 108 (.leaf 382151404) (.leaf 374552931))) (.branch 111 (.branch 110 (.leaf 367112537) (.leaf 359826605)) (.branch 112 (.leaf 352691617) (.leaf 345704149)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 338860870) (.leaf 332158536)) (.branch 116 (.leaf 325593989) (.leaf 319164154))) (.branch 119 (.branch 118 (.leaf 312866036) (.leaf 306696718)) (.branch 120 (.leaf 300653356) (.leaf 294733180)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 164).q*(generalMeanRows 164).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 164).q*(generalMeanRows 164).cutoff/2-2 = (1754/815:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable095.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5042311195) (.branch 2 (.leaf 4867614280) (.leaf 4700947406))) (.branch 5 (.branch 4 (.leaf 4541842249) (.leaf 4389863906)) (.branch 6 (.leaf 4244607975) (.leaf 4105697958)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3972782928) (.leaf 3845535432)) (.branch 10 (.leaf 3723649613) (.leaf 3606839503))) (.branch 13 (.branch 12 (.leaf 3494837484) (.leaf 3387392890)) (.branch 14 (.leaf 3284270740) (.leaf 3185250582))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3090125432) (.branch 17 (.leaf 2998700818) (.leaf 2910793891))) (.branch 20 (.branch 19 (.leaf 2826232616) (.leaf 2744855033)) (.branch 21 (.leaf 2666508566) (.leaf 2591049397)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2518341885) (.leaf 2448258029)) (.branch 25 (.leaf 2380676970) (.leaf 2315484536))) (.branch 28 (.branch 27 (.leaf 2252572812) (.leaf 2191839751)) (.branch 29 (.leaf 2133188804) (.leaf 2076528580)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2021772533) (.branch 32 (.leaf 1968838666) (.leaf 1917649256))) (.branch 35 (.branch 34 (.leaf 1868130598) (.leaf 1820212770)) (.branch 36 (.leaf 1773829408) (.leaf 1728917499)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1685417187) (.leaf 1643271592)) (.branch 40 (.leaf 1602426636) (.leaf 1562830891))) (.branch 43 (.branch 42 (.leaf 1524435426) (.leaf 1487193665)) (.branch 44 (.leaf 1451061261) (.leaf 1415995971))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1381957538) (.branch 47 (.leaf 1348907588) (.leaf 1316809524))) (.branch 50 (.branch 49 (.leaf 1285628433) (.leaf 1255330993)) (.branch 51 (.leaf 1225885391) (.leaf 1197261245)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1169429524) (.leaf 1142362481)) (.branch 55 (.leaf 1116033587) (.leaf 1090417465))) (.branch 58 (.branch 57 (.leaf 1065489836) (.leaf 1041227457)) (.branch 59 (.leaf 1017608076) (.leaf 994610374))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 972213927) (.branch 62 (.leaf 950399152) (.leaf 929147277))) (.branch 65 (.branch 64 (.leaf 908440289) (.leaf 888260907)) (.branch 66 (.leaf 868592542) (.leaf 849419263)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 830725769) (.leaf 812497354)) (.branch 70 (.leaf 794719885) (.leaf 777379770))) (.branch 73 (.branch 72 (.leaf 760463937) (.leaf 743959806)) (.branch 74 (.leaf 727855268) (.leaf 712138666))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 696798769) (.branch 77 (.leaf 681824758) (.leaf 667206206))) (.branch 80 (.branch 79 (.leaf 652933059) (.leaf 638995620)) (.branch 81 (.leaf 625384536) (.leaf 612090781)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 599105639) (.leaf 586420697)) (.branch 85 (.leaf 574027826) (.leaf 561919175))) (.branch 88 (.branch 87 (.leaf 550087153) (.leaf 538524421)) (.branch 89 (.leaf 527223885) (.leaf 516178679)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 505382162) (.branch 92 (.leaf 494827906) (.leaf 484509685))) (.branch 95 (.branch 94 (.leaf 474421473) (.leaf 464557432)) (.branch 96 (.leaf 454911904) (.leaf 445479406)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 436254625) (.leaf 427232405)) (.branch 100 (.leaf 418407749) (.leaf 409775806))) (.branch 103 (.branch 102 (.leaf 401331871) (.leaf 393071376)) (.branch 104 (.leaf 384989887) (.leaf 377083098))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369346827) (.leaf 361777010)) (.branch 108 (.leaf 354369701) (.leaf 347121061))) (.branch 111 (.branch 110 (.leaf 340027361) (.leaf 333084974)) (.branch 112 (.leaf 326290373) (.leaf 319640129)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 313130903) (.leaf 306759447)) (.branch 116 (.leaf 300522603) (.leaf 294417292))) (.branch 119 (.branch 118 (.leaf 288440520) (.leaf 282589371)) (.branch 120 (.leaf 276861003) (.leaf 271252651)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 165).q*(generalMeanRows 165).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 165).q*(generalMeanRows 165).cutoff/2-2 = (1754/815:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable095.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4910130669) (.branch 2 (.leaf 4735167047) (.leaf 4568274026))) (.branch 5 (.branch 4 (.leaf 4408983868) (.leaf 4256862055)) (.branch 6 (.leaf 4111504389) (.leaf 3972534413)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3839601093) (.leaf 3712376740)) (.branch 10 (.leaf 3590555140) (.leaf 3473849863))) (.branch 13 (.branch 12 (.leaf 3361992734) (.leaf 3254732453)) (.branch 14 (.leaf 3151833327) (.leaf 3053074128))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2958247045) (.branch 17 (.leaf 2867156730) (.leaf 2779619415))) (.branch 20 (.branch 19 (.leaf 2695462118) (.leaf 2614521897)) (.branch 21 (.leaf 2536645176) (.leaf 2461687120)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2389511054) (.leaf 2319987935)) (.branch 25 (.leaf 2252995861) (.leaf 2188419607))) (.branch 28 (.branch 27 (.leaf 2126150214) (.leaf 2066084588)) (.branch 29 (.leaf 2008125142) (.leaf 1952179457)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1898159966) (.branch 32 (.leaf 1845983663) (.leaf 1795571830))) (.branch 35 (.branch 34 (.leaf 1746849784) (.leaf 1699746637)) (.branch 36 (.leaf 1654195080) (.leaf 1610131170)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1567494139) (.leaf 1526226216)) (.branch 40 (.leaf 1486272454) (.leaf 1447580571))) (.branch 43 (.branch 42 (.leaf 1410100805) (.leaf 1373785772)) (.branch 44 (.leaf 1338590334) (.leaf 1304471481))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1271388210) (.branch 47 (.leaf 1239301421) (.leaf 1208173811))) (.branch 50 (.branch 49 (.leaf 1177969785) (.leaf 1148655359)) (.branch 51 (.leaf 1120198078) (.leaf 1092566937)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1065732306) (.leaf 1039665855)) (.branch 55 (.leaf 1014340495) (.leaf 989730308))) (.branch 58 (.branch 57 (.leaf 965810490) (.leaf 942557295)) (.branch 59 (.leaf 919947985) (.leaf 897960775))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 876574788) (.branch 62 (.leaf 855770012) (.leaf 835527255))) (.branch 65 (.branch 64 (.leaf 815828109) (.leaf 796654909)) (.branch 66 (.leaf 777990697) (.leaf 759819192)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 742124754) (.leaf 724892358)) (.branch 70 (.leaf 708107560) (.leaf 691756476))) (.branch 73 (.branch 72 (.leaf 675825752) (.leaf 660302540)) (.branch 74 (.leaf 645174477) (.leaf 630429663))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 616056636) (.branch 77 (.leaf 602044359) (.leaf 588382195))) (.branch 80 (.branch 79 (.leaf 575059895) (.leaf 562067576)) (.branch 81 (.leaf 549395707) (.leaf 537035096)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 524976873) (.leaf 513212475)) (.branch 85 (.leaf 501733637) (.leaf 490532375))) (.branch 88 (.branch 87 (.leaf 479600978) (.leaf 468931997)) (.branch 89 (.leaf 458518228) (.leaf 448352710)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 438428710) (.branch 92 (.leaf 428739717) (.leaf 419279428))) (.branch 95 (.branch 94 (.leaf 410041748) (.leaf 401020773)) (.branch 96 (.leaf 392210788) (.leaf 383606258)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375201823) (.leaf 366992286)) (.branch 100 (.leaf 358972613) (.leaf 351137925))) (.branch 103 (.branch 102 (.leaf 343483487) (.leaf 336004712)) (.branch 104 (.leaf 328697148) (.leaf 321556476))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314578504) (.leaf 307759165)) (.branch 108 (.leaf 301094509) (.leaf 294580702))) (.branch 111 (.branch 110 (.leaf 288214018) (.leaf 281990841)) (.branch 112 (.leaf 275907656) (.leaf 269961046)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264147693) (.leaf 258464369)) (.branch 116 (.leaf 252907937) (.leaf 247475346))) (.branch 119 (.branch 118 (.leaf 242163629) (.leaf 236969900)) (.branch 120 (.leaf 231891350) (.leaf 226925248)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 166).q*(generalMeanRows 166).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 166).q*(generalMeanRows 166).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4860823206) (.branch 2 (.leaf 4685203577) (.leaf 4517717290))) (.branch 5 (.branch 4 (.leaf 4357893176) (.leaf 4205293499)) (.branch 6 (.leaf 4059511046) (.leaf 3920166524)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3786906230) (.leaf 3659399961)) (.branch 10 (.leaf 3537339133) (.leaf 3420435075))) (.branch 13 (.branch 12 (.leaf 3308417500) (.leaf 3201033102)) (.branch 14 (.leaf 3098044294) (.leaf 2999228051))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2904374859) (.branch 17 (.leaf 2813287749) (.leaf 2725781420))) (.branch 20 (.branch 19 (.leaf 2641681427) (.leaf 2560823440)) (.branch 21 (.leaf 2483052562) (.leaf 2408222696)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2336195972) (.leaf 2266842203)) (.branch 25 (.leaf 2200038395) (.leaf 2135668288))) (.branch 28 (.branch 27 (.leaf 2073621927) (.leaf 2013795274)) (.branch 29 (.leaf 1956089838) (.leaf 1900412335)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1846674374) (.branch 32 (.leaf 1794792161) (.leaf 1744686225))) (.branch 35 (.branch 34 (.leaf 1696281161) (.leaf 1649505394)) (.branch 36 (.leaf 1604290954) (.leaf 1560573269)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1518290969) (.leaf 1477385705)) (.branch 40 (.leaf 1437801978) (.leaf 1399486980))) (.branch 43 (.branch 42 (.leaf 1362390442) (.leaf 1326464497)) (.branch 44 (.leaf 1291663546) (.leaf 1257944133))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1225264834) (.branch 47 (.leaf 1193586142) (.leaf 1162870368))) (.branch 50 (.branch 49 (.leaf 1133081545) (.leaf 1104185334)) (.branch 51 (.leaf 1076148941) (.leaf 1048941036)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1022531678) (.leaf 996892242)) (.branch 55 (.leaf 971995354) (.leaf 947814825))) (.branch 58 (.branch 57 (.leaf 924325593) (.leaf 901503664)) (.branch 59 (.leaf 879326063) (.leaf 857770781))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 836816725) (.branch 62 (.leaf 816443677) (.leaf 796632252))) (.branch 65 (.branch 64 (.leaf 777363852) (.leaf 758620636)) (.branch 66 (.leaf 740385476) (.leaf 722641931)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 705374207) (.leaf 688567132)) (.branch 70 (.leaf 672206126) (.leaf 656277172))) (.branch 73 (.branch 72 (.leaf 640766790) (.leaf 625662015)) (.branch 74 (.leaf 610950371) (.leaf 596619852))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 582658897) (.branch 77 (.leaf 569056371) (.leaf 555801551))) (.branch 80 (.branch 79 (.leaf 542884100) (.leaf 530294057)) (.branch 81 (.leaf 518021817) (.leaf 506058116)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 494394018) (.leaf 483020899)) (.branch 85 (.leaf 471930436) (.leaf 461114592))) (.branch 88 (.branch 87 (.leaf 450565606) (.leaf 440275980)) (.branch 89 (.leaf 430238470) (.leaf 420446074)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 410892022) (.branch 92 (.leaf 401569770) (.leaf 392472985))) (.branch 95 (.branch 94 (.leaf 383595542) (.leaf 374931515)) (.branch 96 (.leaf 366475166) (.leaf 358220939)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 350163456) (.leaf 342297507)) (.branch 100 (.leaf 334618045) (.leaf 327120176))) (.branch 103 (.branch 102 (.leaf 319799162) (.leaf 312650405)) (.branch 104 (.leaf 305669449) (.leaf 298851972))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292193781) (.leaf 285690808)) (.branch 108 (.leaf 279339105) (.leaf 273134841))) (.branch 111 (.branch 110 (.leaf 267074295) (.leaf 261153857)) (.branch 112 (.leaf 255370017) (.leaf 249719370)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244198605) (.leaf 238804507)) (.branch 116 (.leaf 233533948) (.leaf 228383892))) (.branch 119 (.branch 118 (.leaf 223351385) (.leaf 218433555)) (.branch 120 (.leaf 213627611) (.leaf 208930835)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 167).q*(generalMeanRows 167).c/2-2 = (343/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable096.value]
    have hcontinuation : (generalMeanRows 167).q*(generalMeanRows 167).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4903861391) (.branch 2 (.leaf 4728997949) (.leaf 4562233683))) (.branch 5 (.branch 4 (.leaf 4403096853) (.leaf 4251149325)) (.branch 6 (.leaf 4105983640) (.leaf 3967220402)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3834505927) (.leaf 3707510147)) (.branch 10 (.leaf 3585924712) (.leaf 3469461279))) (.branch 13 (.branch 12 (.leaf 3357849962) (.leaf 3250837935)) (.branch 14 (.leaf 3148188148) (.leaf 3049678169))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2955099125) (.branch 17 (.leaf 2864254729) (.leaf 2776960394))) (.branch 20 (.branch 19 (.leaf 2693042420) (.leaf 2612337247)) (.branch 21 (.leaf 2534690764) (.leaf 2459957681)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2388000940) (.leaf 2318691179)) (.branch 25 (.leaf 2251906232) (.leaf 2187530669))) (.branch 28 (.branch 27 (.leaf 2125455365) (.leaf 2065577110)) (.branch 29 (.leaf 2007798234) (.leaf 1952026270)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1898173635) (.branch 32 (.leaf 1846157333) (.leaf 1795898680))) (.branch 35 (.branch 34 (.leaf 1747323048) (.leaf 1700359624)) (.branch 36 (.leaf 1654941186) (.leaf 1611003897)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1568487107) (.leaf 1527333169)) (.branch 40 (.leaf 1487487274) (.leaf 1448897283))) (.branch 43 (.branch 42 (.leaf 1411513583) (.leaf 1375288945)) (.branch 44 (.leaf 1340178390) (.leaf 1306139069))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1273130141) (.branch 47 (.leaf 1241112672) (.leaf 1210049526))) (.branch 50 (.branch 49 (.leaf 1179905271) (.leaf 1150646089)) (.branch 51 (.leaf 1122239689) (.leaf 1094655229)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1067863237) (.leaf 1041835545)) (.branch 55 (.leaf 1016545217) (.leaf 991966489))) (.branch 58 (.branch 57 (.leaf 968074707) (.leaf 944846274)) (.branch 59 (.leaf 922258593) (.leaf 900290021))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 878919817) (.branch 62 (.leaf 858128102) (.leaf 837895816))) (.branch 65 (.branch 64 (.leaf 818204674) (.leaf 799037135)) (.branch 66 (.leaf 780376358) (.leaf 762206178)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 744511066) (.leaf 727276104)) (.branch 70 (.leaf 710486952) (.leaf 694129825))) (.branch 73 (.branch 72 (.leaf 678191466) (.leaf 662659121)) (.branch 74 (.leaf 647520516) (.leaf 632763836))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 618377703) (.branch 77 (.leaf 604351159) (.leaf 590673645))) (.branch 80 (.branch 79 (.leaf 577334983) (.leaf 564325362)) (.branch 81 (.leaf 551635318) (.leaf 539255723)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 527177768) (.leaf 515392950)) (.branch 85 (.leaf 503893060) (.leaf 492670169))) (.branch 88 (.branch 87 (.leaf 481716616) (.leaf 471025001)) (.branch 89 (.leaf 460588167) (.leaf 450399198)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440451403) (.branch 92 (.leaf 430738309) (.leaf 421253655))) (.branch 95 (.branch 94 (.leaf 411991379) (.leaf 402945614)) (.branch 96 (.leaf 394110676) (.leaf 385481062)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377051440) (.leaf 368816642)) (.branch 100 (.leaf 360771659) (.leaf 352911636))) (.branch 103 (.branch 102 (.leaf 345231864) (.leaf 337727776)) (.branch 104 (.leaf 330394941) (.leaf 323229059))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316225957) (.leaf 309381584)) (.branch 108 (.leaf 302692006) (.leaf 296153405))) (.branch 111 (.branch 110 (.leaf 289762069) (.leaf 283514394)) (.branch 112 (.leaf 277406877) (.leaf 271436113)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265598793) (.leaf 259891701)) (.branch 116 (.leaf 254311708) (.leaf 248855770))) (.branch 119 (.branch 118 (.leaf 243520928) (.leaf 238304303)) (.branch 120 (.leaf 233203092) (.leaf 228214570)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 168).q*(generalMeanRows 168).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 168).q*(generalMeanRows 168).cutoff/2-2 = (1754/815:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable095.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4853586287) (.branch 2 (.leaf 4678086004) (.leaf 4510747010))) (.branch 5 (.branch 4 (.leaf 4351094166) (.leaf 4198686154)) (.branch 6 (.leaf 4053112525) (.leaf 3913991073)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3780965474) (.leaf 3653703168)) (.branch 10 (.leaf 3531893455) (.leaf 3415245775))) (.branch 13 (.branch 12 (.leaf 3303488146) (.leaf 3196365758)) (.branch 14 (.leaf 3093639682) (.leaf 2995085706))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2900493267) (.branch 17 (.leaf 2809664476) (.leaf 2722413221))) (.branch 20 (.branch 19 (.leaf 2638564357) (.leaf 2557952944)) (.branch 21 (.leaf 2480423563) (.leaf 2405829675)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2334033034) (.leaf 2264903143)) (.branch 25 (.leaf 2198316757) (.leaf 2134157415))) (.branch 28 (.branch 27 (.leaf 2072315009) (.leaf 2012685389)) (.branch 29 (.leaf 1955169989) (.leaf 1899675486)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1846113478) (.branch 32 (.leaf 1794400186) (.leaf 1744456181))) (.branch 35 (.branch 34 (.leaf 1696206117) (.leaf 1649578500)) (.branch 36 (.leaf 1604505454) (.leaf 1560922515)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1518768436) (.leaf 1477984998)) (.branch 40 (.leaf 1438516843) (.leaf 1400311309))) (.branch 43 (.branch 42 (.leaf 1363318282) (.leaf 1327490051)) (.branch 44 (.leaf 1292781180) (.leaf 1259148378))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1226550387) (.branch 47 (.leaf 1194947868) (.leaf 1164303301))) (.branch 50 (.branch 49 (.leaf 1134580885) (.leaf 1105746450)) (.branch 51 (.leaf 1077767368) (.leaf 1050612475)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1024251991) (.leaf 998657453)) (.branch 55 (.leaf 973801643) (.leaf 949658529))) (.branch 58 (.branch 57 (.leaf 926203199) (.leaf 903411811)) (.branch 59 (.leaf 881261533) (.leaf 859730498))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 838797753) (.branch 62 (.leaf 818443214) (.leaf 798647627))) (.branch 65 (.branch 64 (.leaf 779392522) (.leaf 760660180)) (.branch 66 (.leaf 742433595) (.leaf 724696440)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 707433034) (.leaf 690628315)) (.branch 70 (.leaf 674267806) (.leaf 658337591))) (.branch 73 (.branch 72 (.leaf 642824290) (.leaf 627715030)) (.branch 74 (.leaf 612997427) (.leaf 598659560))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 584689953) (.branch 77 (.leaf 571077553) (.leaf 557811711))) (.branch 80 (.branch 79 (.leaf 544882168) (.leaf 532279031)) (.branch 81 (.leaf 519992765) (.leaf 508014171)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 496334376) (.leaf 484944815)) (.branch 85 (.leaf 473837221) (.leaf 463003614))) (.branch 88 (.branch 87 (.leaf 452436283) (.leaf 442127782)) (.branch 89 (.leaf 432070912) (.leaf 422258717)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 412684471) (.branch 92 (.leaf 403341669) (.leaf 394224019))) (.branch 95 (.branch 94 (.leaf 385325433) (.leaf 376640018)) (.branch 96 (.leaf 368162069) (.leaf 359886064)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351806654) (.leaf 343918657)) (.branch 100 (.leaf 336217051) (.leaf 328696971))) (.branch 103 (.branch 102 (.leaf 321353700) (.leaf 314182663)) (.branch 104 (.leaf 307179426) (.leaf 300339686))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 293659269) (.leaf 287134125)) (.branch 108 (.leaf 280760323) (.leaf 274534046))) (.branch 111 (.branch 110 (.leaf 268451588) (.leaf 262509353)) (.branch 112 (.leaf 256703844) (.leaf 251031666)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 245489520) (.leaf 240074200)) (.branch 116 (.leaf 234782590) (.leaf 229611660))) (.branch 119 (.branch 118 (.leaf 224558465) (.leaf 219620140)) (.branch 120 (.leaf 214793901) (.leaf 210077036)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 169).q*(generalMeanRows 169).c/2-2 = (343/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable096.value]
    have hcontinuation : (generalMeanRows 169).q*(generalMeanRows 169).cutoff/2-2 = (1754/815:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable095.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5243211813) (.branch 2 (.leaf 5076207539) (.leaf 4916761041))) (.branch 5 (.branch 4 (.leaf 4764426274) (.leaf 4618789336)) (.branch 6 (.leaf 4479465656) (.leaf 4346097490)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4218351670) (.leaf 4095917592)) (.branch 10 (.leaf 3978505389) (.leaf 3865844297))) (.branch 13 (.branch 12 (.leaf 3757681161) (.leaf 3653779093)) (.branch 14 (.leaf 3553916244) (.leaf 3457884687))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3365489397) (.branch 17 (.leaf 3276547324) (.leaf 3190886536))) (.branch 20 (.branch 19 (.leaf 3108345441) (.leaf 3028772067)) (.branch 21 (.leaf 2952023401) (.leaf 2877964783)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2806469344) (.leaf 2737417490)) (.branch 25 (.leaf 2670696421) (.leaf 2606199692))) (.branch 28 (.branch 27 (.leaf 2543826802) (.leaf 2483482814)) (.branch 29 (.leaf 2425078001) (.leaf 2368527525)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2313751123) (.branch 32 (.leaf 2260672834) (.leaf 2209220729))) (.branch 35 (.branch 34 (.leaf 2159326672) (.leaf 2110926083)) (.branch 36 (.leaf 2063957734) (.leaf 2018363542)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1974088389) (.leaf 1931079946)) (.branch 40 (.leaf 1889288510) (.leaf 1848666853))) (.branch 43 (.branch 42 (.leaf 1809170080) (.leaf 1770755496)) (.branch 44 (.leaf 1733382479) (.leaf 1697012367))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1661608345) (.branch 47 (.leaf 1627135343) (.leaf 1593559942))) (.branch 50 (.branch 49 (.leaf 1560850278) (.leaf 1528975964)) (.branch 51 (.leaf 1497908002) (.leaf 1467618715)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1438081670) (.leaf 1409271619)) (.branch 55 (.leaf 1381164428) (.leaf 1353737023))) (.branch 58 (.branch 57 (.leaf 1326967336) (.leaf 1300834247)) (.branch 59 (.leaf 1275317541) (.leaf 1250397856))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1226056645) (.branch 62 (.leaf 1202276128) (.leaf 1179039261))) (.branch 65 (.branch 64 (.leaf 1156329691) (.leaf 1134131729)) (.branch 66 (.leaf 1112430311) (.leaf 1091210971)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1070459810) (.leaf 1050163469)) (.branch 70 (.leaf 1030309104) (.leaf 1010884358))) (.branch 73 (.branch 72 (.leaf 991877342) (.leaf 973276610)) (.branch 74 (.leaf 955071140) (.leaf 937250311))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 919803888) (.branch 77 (.leaf 902722005) (.leaf 885995141))) (.branch 80 (.branch 79 (.leaf 869614114) (.leaf 853570059)) (.branch 81 (.leaf 837854417) (.leaf 822458919)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 807375574) (.leaf 792596661)) (.branch 85 (.leaf 778114711) (.leaf 763922499))) (.branch 88 (.branch 87 (.leaf 750013034) (.leaf 736379548)) (.branch 89 (.leaf 723015490) (.leaf 709914510)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 697070458) (.branch 92 (.leaf 684477372) (.leaf 672129471))) (.branch 95 (.branch 94 (.leaf 660021149) (.leaf 648146964)) (.branch 96 (.leaf 636501637) (.leaf 625080043)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 613877204) (.leaf 602888285)) (.branch 100 (.leaf 592108588) (.leaf 581533547))) (.branch 103 (.branch 102 (.leaf 571158721) (.leaf 560979795)) (.branch 104 (.leaf 550992568) (.leaf 541192954))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 531576976) (.leaf 522140764)) (.branch 108 (.leaf 512880548) (.leaf 503792655))) (.branch 111 (.branch 110 (.leaf 494873510) (.leaf 486119628)) (.branch 112 (.leaf 477527611) (.leaf 469094148)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 460816012) (.leaf 452690051)) (.branch 116 (.leaf 444713196) (.leaf 436882450))) (.branch 119 (.branch 118 (.leaf 429194887) (.leaf 421647653)) (.branch 120 (.leaf 414237963) (.leaf 406963094)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 170).q*(generalMeanRows 170).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 170).q*(generalMeanRows 170).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5277960486) (.branch 2 (.leaf 5109849414) (.leaf 4949346206))) (.branch 5 (.branch 4 (.leaf 4796001862) (.leaf 4649399734)) (.branch 6 (.leaf 4509152706) (.leaf 4374900660)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4246308222) (.leaf 4123062729)) (.branch 10 (.leaf 4004872393) (.leaf 3891464654))) (.branch 13 (.branch 12 (.leaf 3782584682) (.leaf 3677994017)) (.branch 14 (.leaf 3577469341) (.leaf 3480801347))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3387793720) (.branch 17 (.leaf 3298262195) (.leaf 3212033703))) (.branch 20 (.branch 19 (.leaf 3128945578) (.leaf 3048844842)) (.branch 21 (.leaf 2971587535) (.leaf 2897038103)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2825068838) (.leaf 2755559352)) (.branch 25 (.leaf 2688396098) (.leaf 2623471926))) (.branch 28 (.branch 27 (.leaf 2560685668) (.leaf 2499941758)) (.branch 29 (.leaf 2441149876) (.leaf 2384224619)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2329085194) (.branch 32 (.leaf 2275655135) (.leaf 2223862039))) (.branch 35 (.branch 34 (.leaf 2173637316) (.leaf 2124915959)) (.branch 36 (.leaf 2077636333) (.leaf 2031739972)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1987171391) (.leaf 1943877916)) (.branch 40 (.leaf 1901809513) (.leaf 1860918641))) (.branch 43 (.branch 42 (.leaf 1821160109) (.leaf 1782490937)) (.branch 44 (.leaf 1744870236) (.leaf 1708259085))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1672620428) (.branch 47 (.leaf 1637918961) (.leaf 1604121044))) (.branch 50 (.branch 49 (.leaf 1571194601) (.leaf 1539109044)) (.branch 51 (.leaf 1507835184) (.leaf 1477345158)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1447612361) (.leaf 1418611375)) (.branch 55 (.leaf 1390317907) (.leaf 1362708731))) (.branch 58 (.branch 57 (.leaf 1335761631) (.leaf 1309455349)) (.branch 59 (.leaf 1283769534) (.leaf 1258684698))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1234182168) (.branch 62 (.leaf 1210244050) (.leaf 1186853183))) (.branch 65 (.branch 64 (.leaf 1163993109) (.leaf 1141648033)) (.branch 66 (.leaf 1119802792) (.leaf 1098442823)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1077554137) (.leaf 1057123285)) (.branch 70 (.leaf 1037137337) (.leaf 1017583856))) (.branch 73 (.branch 72 (.leaf 998450874) (.leaf 979726869)) (.branch 74 (.leaf 961400744) (.leaf 943461810))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 925899764) (.branch 77 (.leaf 908704672) (.leaf 891866953))) (.branch 80 (.branch 79 (.leaf 875377364) (.leaf 859226979)) (.branch 81 (.leaf 843407183) (.leaf 827909653)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 812726346) (.leaf 797849488)) (.branch 85 (.leaf 783271561) (.leaf 768985291))) (.branch 88 (.branch 87 (.leaf 754983643) (.leaf 741259804)) (.branch 89 (.leaf 727807176) (.leaf 714619372)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 701690198) (.branch 92 (.leaf 689013653) (.leaf 676583918))) (.branch 95 (.branch 94 (.leaf 664395349) (.leaf 652442470)) (.branch 96 (.leaf 640719965) (.leaf 629222676)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 617945592) (.leaf 606883845)) (.branch 100 (.leaf 596032707) (.leaf 585387581))) (.branch 103 (.branch 102 (.leaf 574943998) (.leaf 564697612)) (.branch 104 (.leaf 554644196) (.leaf 544779636))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535099930) (.leaf 525601181)) (.branch 108 (.leaf 516279594) (.leaf 507131472))) (.branch 111 (.branch 110 (.leaf 498153217) (.leaf 489341320)) (.branch 112 (.leaf 480692360) (.leaf 472203006)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 463870007) (.leaf 455690193)) (.branch 116 (.leaf 447660473) (.leaf 439777829))) (.branch 119 (.branch 118 (.leaf 432039318) (.leaf 424442066)) (.branch 120 (.leaf 416983269) (.leaf 409660187)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 171).q*(generalMeanRows 171).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 171).q*(generalMeanRows 171).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4929966858) (.branch 2 (.leaf 4754070945) (.leaf 4586355125))) (.branch 5 (.branch 4 (.leaf 4426340541) (.leaf 4273582558)) (.branch 6 (.leaf 4127667778) (.leaf 3988211375)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3854854706) (.leaf 3727263167)) (.branch 10 (.leaf 3605124264) (.leaf 3488145866))) (.branch 13 (.branch 12 (.leaf 3376054627) (.leaf 3268594557)) (.branch 14 (.leaf 3165525720) (.leaf 3066623046))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2971675252) (.branch 17 (.leaf 2880483855) (.leaf 2792862264))) (.branch 20 (.branch 19 (.leaf 2708634951) (.leaf 2627636691)) (.branch 21 (.leaf 2549711857) (.leaf 2474713777)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2402504139) (.leaf 2332952438)) (.branch 25 (.leaf 2265935473) (.leaf 2201336872))) (.branch 28 (.branch 27 (.leaf 2139046659) (.leaf 2078960851)) (.branch 29 (.leaf 2020981081) (.leaf 1965014249)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1910972204) (.branch 32 (.leaf 1858771436) (.leaf 1808332799))) (.branch 35 (.branch 34 (.leaf 1759581251) (.leaf 1712445605)) (.branch 36 (.leaf 1666858310) (.leaf 1622755227)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1580075444) (.leaf 1538761077)) (.branch 40 (.leaf 1498757107) (.leaf 1460011213))) (.branch 43 (.branch 42 (.leaf 1422473617) (.leaf 1386096947)) (.branch 44 (.leaf 1350836101) (.leaf 1316648118))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1283492067) (.branch 47 (.leaf 1251328931) (.leaf 1220121505))) (.branch 50 (.branch 49 (.leaf 1189834300) (.leaf 1160433446)) (.branch 51 (.leaf 1131886614) (.leaf 1104162927)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1077232889) (.leaf 1051068310)) (.branch 55 (.leaf 1025642238) (.leaf 1000928899))) (.branch 58 (.branch 57 (.leaf 976903633) (.leaf 953542837)) (.branch 59 (.leaf 930823915) (.leaf 908725224))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 887226030) (.branch 62 (.leaf 866306459) (.leaf 845947455))) (.branch 65 (.branch 64 (.leaf 826130745) (.leaf 806838793)) (.branch 66 (.leaf 788054772) (.leaf 769762525)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 751946533) (.leaf 734591889)) (.branch 70 (.leaf 717684264) (.leaf 701209884))) (.branch 73 (.branch 72 (.leaf 685155500) (.leaf 669508368)) (.branch 74 (.leaf 654256225) (.leaf 639387262))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 624890113) (.branch 77 (.leaf 610753824) (.leaf 596967844))) (.branch 80 (.branch 79 (.leaf 583522001) (.leaf 570406490)) (.branch 81 (.leaf 557611851) (.leaf 545128960)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 532949012) (.leaf 521063507)) (.branch 85 (.leaf 509464235) (.leaf 498143270))) (.branch 88 (.branch 87 (.leaf 487092951) (.leaf 476305876)) (.branch 89 (.leaf 465774890) (.leaf 455493071)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 445453728) (.branch 92 (.leaf 435650385) (.leaf 426076776))) (.branch 95 (.branch 94 (.leaf 416726834) (.leaf 407594686)) (.branch 96 (.leaf 398674645) (.leaf 389961200)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 381449011) (.leaf 373132905)) (.branch 100 (.leaf 365007865) (.leaf 357069026))) (.branch 103 (.branch 102 (.leaf 349311671) (.leaf 341731224)) (.branch 104 (.leaf 334323243) (.leaf 327083420))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 320007572) (.leaf 313091635)) (.branch 108 (.leaf 306331667) (.leaf 299723836))) (.branch 111 (.branch 110 (.leaf 293264421) (.leaf 286949804)) (.branch 112 (.leaf 280776471) (.leaf 274741006)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 268840087) (.leaf 263070485)) (.branch 116 (.leaf 257429057) (.leaf 251912750))) (.branch 119 (.branch 118 (.leaf 246518589) (.leaf 241243684)) (.branch 120 (.leaf 236085218) (.leaf 231040451)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 172).q*(generalMeanRows 172).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 172).q*(generalMeanRows 172).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5175444437) (.branch 2 (.leaf 4996069888) (.leaf 4824973857))) (.branch 5 (.branch 4 (.leaf 4661671066) (.leaf 4505710978)) (.branch 6 (.leaf 4356674763) (.leaf 4214172594)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4077841222) (.leaf 3947341796)) (.branch 10 (.leaf 3822357902) (.leaf 3702593796))) (.branch 13 (.branch 12 (.leaf 3587772793) (.leaf 3477635822)) (.branch 14 (.leaf 3371940095) (.leaf 3270457913))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3172975560) (.branch 17 (.leaf 3079292302) (.leaf 2989219469))) (.branch 20 (.branch 19 (.leaf 2902579610) (.leaf 2819205719)) (.branch 21 (.leaf 2738940524) (.leaf 2661635829)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2587151914) (.leaf 2515356970)) (.branch 25 (.leaf 2446126590) (.leaf 2379343284))) (.branch 28 (.branch 27 (.leaf 2314896046) (.leaf 2252679933)) (.branch 29 (.leaf 2192595695) (.leaf 2134549415)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2078452181) (.branch 32 (.leaf 2024219782) (.leaf 1971772423))) (.branch 35 (.branch 34 (.leaf 1921034460) (.leaf 1871934151)) (.branch 36 (.leaf 1824403424) (.leaf 1778377668)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1733795523) (.leaf 1690598697)) (.branch 40 (.leaf 1648731789) (.leaf 1608142124))) (.branch 43 (.branch 42 (.leaf 1568779597) (.leaf 1530596530)) (.branch 44 (.leaf 1493547536) (.leaf 1457589393))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1422680922) (.branch 47 (.leaf 1388782876) (.leaf 1355857837))) (.branch 50 (.branch 49 (.leaf 1323870113) (.leaf 1292785649)) (.branch 51 (.leaf 1262571939) (.leaf 1233197940)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1204633999) (.leaf 1176851779)) (.branch 55 (.leaf 1149824190) (.leaf 1123525323))) (.branch 58 (.branch 57 (.leaf 1097930393) (.leaf 1073015678)) (.branch 59 (.leaf 1048758465) (.leaf 1025137003))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1002130451) (.branch 62 (.leaf 979718830) (.leaf 957882989))) (.branch 65 (.branch 64 (.leaf 936604556) (.leaf 915865903)) (.branch 66 (.leaf 895650109) (.leaf 875940929)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 856722757) (.leaf 837980596)) (.branch 70 (.leaf 819700034) (.leaf 801867210))) (.branch 73 (.branch 72 (.leaf 784468794) (.leaf 767491957)) (.branch 74 (.leaf 750924351) (.leaf 734754088))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718969715) (.branch 77 (.leaf 703560199) (.leaf 688514904))) (.branch 80 (.branch 79 (.leaf 673823577) (.leaf 659476327)) (.branch 81 (.leaf 645463613) (.leaf 631776226)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618405277) (.leaf 605342180)) (.branch 85 (.leaf 592578641) (.leaf 580106648))) (.branch 88 (.branch 87 (.leaf 567918454) (.leaf 556006569)) (.branch 89 (.leaf 544363750) (.leaf 532982990)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521857505) (.branch 92 (.leaf 510980732) (.leaf 500346314))) (.branch 95 (.branch 94 (.leaf 489948095) (.leaf 479780110)) (.branch 96 (.leaf 469836579) (.leaf 460111901)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450600643) (.leaf 441297537)) (.branch 100 (.leaf 432197473) (.leaf 423295492))) (.branch 103 (.branch 102 (.leaf 414586783) (.leaf 406066673)) (.branch 104 (.leaf 397730626) (.leaf 389574238))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381593228) (.leaf 373783439)) (.branch 108 (.leaf 366140828) (.leaf 358661469))) (.branch 111 (.branch 110 (.leaf 351341541) (.leaf 344177331)) (.branch 112 (.leaf 337165226) (.leaf 330301712)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 323583369) (.leaf 317006869)) (.branch 116 (.leaf 310568974) (.leaf 304266529))) (.branch 119 (.branch 118 (.leaf 298096463) (.leaf 292055786)) (.branch 120 (.leaf 286141584) (.leaf 280351020)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 173).q*(generalMeanRows 173).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 173).q*(generalMeanRows 173).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5253353553) (.branch 2 (.leaf 5083288480) (.leaf 4920942226))) (.branch 5 (.branch 4 (.leaf 4765859880) (.leaf 4617619284)) (.branch 6 (.leaf 4475828168) (.leaf 4340121595)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4210159677) (.leaf 4085625511)) (.branch 10 (.leaf 3966223333) (.leaf 3851676838))) (.branch 13 (.branch 12 (.leaf 3741727674) (.leaf 3636134061)) (.branch 14 (.leaf 3534669548) (.leaf 3437121869))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3343291914) (.branch 17 (.leaf 3252992774) (.leaf 3166048872))) (.branch 20 (.branch 19 (.leaf 3082295173) (.leaf 3001576446)) (.branch 21 (.leaf 2923746595) (.leaf 2848668038)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2776211137) (.leaf 2706253672)) (.branch 25 (.leaf 2638680351) (.leaf 2573382361))) (.branch 28 (.branch 27 (.leaf 2510256951) (.leaf 2449207045)) (.branch 29 (.leaf 2390140883) (.leaf 2332971687)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2277617353) (.branch 32 (.leaf 2224000162) (.leaf 2172046509))) (.branch 35 (.branch 34 (.leaf 2121686659) (.leaf 2072854509)) (.branch 36 (.leaf 2025487376) (.leaf 1979525786)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1934913295) (.leaf 1891596302)) (.branch 40 (.leaf 1849523892) (.leaf 1808647676))) (.branch 43 (.branch 42 (.leaf 1768921648) (.leaf 1730302049)) (.branch 44 (.leaf 1692747239) (.leaf 1656217580))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1620675322) (.branch 47 (.leaf 1586084500) (.leaf 1552410834))) (.branch 50 (.branch 49 (.leaf 1519621637) (.leaf 1487685730)) (.branch 51 (.leaf 1456573356) (.leaf 1426256109)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1396706858) (.leaf 1367899681)) (.branch 55 (.leaf 1339809798) (.leaf 1312413516))) (.branch 58 (.branch 57 (.leaf 1285688170) (.leaf 1259612065)) (.branch 59 (.leaf 1234164436) (.leaf 1209325391))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1185075870) (.branch 62 (.leaf 1161397605) (.leaf 1138273077))) (.branch 65 (.branch 64 (.leaf 1115685480) (.leaf 1093618686)) (.branch 66 (.leaf 1072057209) (.leaf 1050986177)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1030391301) (.leaf 1010258845)) (.branch 70 (.leaf 990575601) (.leaf 971328863))) (.branch 73 (.branch 72 (.leaf 952506405) (.leaf 934096457)) (.branch 74 (.leaf 916087682) (.leaf 898469159))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 881230362) (.branch 77 (.leaf 864361143) (.leaf 847851714))) (.branch 80 (.branch 79 (.leaf 831692630) (.leaf 815874775)) (.branch 81 (.leaf 800389348) (.leaf 785227846)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 770382054) (.leaf 755844033)) (.branch 85 (.leaf 741606104) (.leaf 727660841))) (.branch 88 (.branch 87 (.leaf 714001058) (.leaf 700619800)) (.branch 89 (.leaf 687510333) (.leaf 674666134)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 662080886) (.branch 92 (.leaf 649748462) (.leaf 637662926))) (.branch 95 (.branch 94 (.leaf 625818520) (.leaf 614209659)) (.branch 96 (.leaf 602830923) (.leaf 591677051)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 580742936) (.leaf 570023618)) (.branch 100 (.leaf 559514278) (.leaf 549210232))) (.branch 103 (.branch 102 (.leaf 539106931) (.leaf 529199948)) (.branch 104 (.leaf 519484981) (.leaf 509957843))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 500614462) (.leaf 491450874)) (.branch 108 (.leaf 482463220) (.leaf 473647744))) (.branch 111 (.branch 110 (.leaf 465000786) (.leaf 456518782)) (.branch 112 (.leaf 448198261) (.leaf 440035836)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 432028211) (.leaf 424172168)) (.branch 116 (.leaf 416464571) (.leaf 408902362))) (.branch 119 (.branch 118 (.leaf 401482557) (.leaf 394202245)) (.branch 120 (.leaf 387058584) (.leaf 380048802)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 174).q*(generalMeanRows 174).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    have hcontinuation : (generalMeanRows 174).q*(generalMeanRows 174).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5419273413) (.branch 2 (.leaf 5246661309) (.leaf 5081860764))) (.branch 5 (.branch 4 (.leaf 4924410754) (.leaf 4773883479)) (.branch 6 (.leaf 4629881455) (.leaf 4492034924)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4359999533) (.leaf 4233454245)) (.branch 10 (.leaf 4112099463) (.leaf 3995655328))) (.branch 13 (.branch 12 (.leaf 3883860187) (.leaf 3776469196)) (.branch 14 (.leaf 3673253056) (.leaf 3573996859))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3478499031) (.branch 17 (.leaf 3386570375) (.leaf 3298033188))) (.branch 20 (.branch 19 (.leaf 3212720449) (.leaf 3130475084)) (.branch 21 (.leaf 3051149277) (.leaf 2974603848)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2900707666) (.leaf 2829337122)) (.branch 25 (.leaf 2760375629) (.leaf 2693713167))) (.branch 28 (.branch 27 (.leaf 2629245861) (.leaf 2566875584)) (.branch 29 (.leaf 2506509599) (.leaf 2448060216)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2391444479) (.branch 32 (.leaf 2336583876) (.leaf 2283404064))) (.branch 35 (.branch 34 (.leaf 2231834616) (.leaf 2181808786)) (.branch 36 (.leaf 2133263288) (.leaf 2086138091)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2040376224) (.leaf 1995923603)) (.branch 40 (.leaf 1952728854) (.leaf 1910743164))) (.branch 43 (.branch 42 (.leaf 1869920130) (.leaf 1830215624)) (.branch 44 (.leaf 1791587660) (.leaf 1753996277))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1717403425) (.branch 47 (.leaf 1681772856) (.leaf 1647070027))) (.branch 50 (.branch 49 (.leaf 1613262008) (.leaf 1580317387)) (.branch 51 (.leaf 1548206195) (.leaf 1516899825)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1486370957) (.leaf 1456593494)) (.branch 55 (.leaf 1427542493) (.leaf 1399194105))) (.branch 58 (.branch 57 (.leaf 1371525519) (.leaf 1344514908)) (.branch 59 (.leaf 1318141378) (.leaf 1292384916))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1267226352) (.branch 62 (.leaf 1242647310) (.leaf 1218630173))) (.branch 65 (.branch 64 (.leaf 1195158040) (.leaf 1172214693)) (.branch 66 (.leaf 1149784564) (.leaf 1127852701)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1106404737) (.leaf 1085426866)) (.branch 70 (.leaf 1064905812) (.leaf 1044828803))) (.branch 73 (.branch 72 (.leaf 1025183552) (.leaf 1005958227)) (.branch 74 (.leaf 987141435) (.leaf 968722202))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 950689946) (.branch 77 (.leaf 933034471) (.leaf 915745937))) (.branch 80 (.branch 79 (.leaf 898814852) (.leaf 882232054)) (.branch 81 (.leaf 865988697) (.leaf 850076234)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 834486407) (.leaf 819211233)) (.branch 85 (.leaf 804242994) (.leaf 789574222))) (.branch 88 (.branch 87 (.leaf 775197691) (.leaf 761106408)) (.branch 89 (.leaf 747293598) (.leaf 733752701)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 720477359) (.branch 92 (.leaf 707461410) (.leaf 694698880))) (.branch 95 (.branch 94 (.leaf 682183972) (.leaf 669911065)) (.branch 96 (.leaf 657874700) (.leaf 646069581)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 634490562) (.leaf 623132647)) (.branch 100 (.leaf 611990979) (.leaf 601060838))) (.branch 103 (.branch 102 (.leaf 590337637) (.leaf 579816913)) (.branch 104 (.leaf 569494325) (.leaf 559365650))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 549426778) (.leaf 539673708)) (.branch 108 (.leaf 530102543) (.leaf 520709489))) (.branch 111 (.branch 110 (.leaf 511490848) (.leaf 502443019)) (.branch 112 (.leaf 493562492) (.leaf 484845842)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 476289734) (.leaf 467890913)) (.branch 116 (.leaf 459646203) (.leaf 451552508))) (.branch 119 (.branch 118 (.leaf 443606805) (.leaf 435806143)) (.branch 120 (.leaf 428147643) (.leaf 420628492)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 175).q*(generalMeanRows 175).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 175).q*(generalMeanRows 175).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4868479578) (.branch 2 (.leaf 4692222480) (.leaf 4524228193))) (.branch 5 (.branch 4 (.leaf 4364010810) (.leaf 4211119232)) (.branch 6 (.leaf 4065134132) (.leaf 3925665247)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3792348944) (.leaf 3664846037)) (.branch 10 (.leaf 3542839826) (.leaf 3426034316))) (.branch 13 (.branch 12 (.leaf 3314152610) (.leaf 3206935458)) (.branch 14 (.leaf 3104139923) (.leaf 3005538178))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2910916409) (.branch 17 (.leaf 2820073798) (.leaf 2732821613))) (.branch 20 (.branch 19 (.leaf 2648982355) (.leaf 2568388983)) (.branch 21 (.leaf 2490884204) (.leaf 2416319810)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2344556076) (.leaf 2275461199)) (.branch 25 (.leaf 2208910782) (.leaf 2144787352))) (.branch 28 (.branch 27 (.leaf 2082979922) (.leaf 2023383576)) (.branch 29 (.leaf 1965899089) (.leaf 1910432576)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1856895155) (.branch 32 (.leaf 1805202651) (.leaf 1755275302))) (.branch 35 (.branch 34 (.leaf 1707037501) (.leaf 1660417540)) (.branch 36 (.leaf 1615347388) (.leaf 1571762467)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1529601458) (.leaf 1488806105)) (.branch 40 (.leaf 1449321044) (.leaf 1411093639))) (.branch 43 (.branch 42 (.leaf 1374073822) (.leaf 1338213953)) (.branch 44 (.leaf 1303468684) (.leaf 1269794830))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1237151249) (.branch 47 (.leaf 1205498735) (.leaf 1174799906))) (.branch 50 (.branch 49 (.leaf 1145019112) (.leaf 1116122336)) (.branch 51 (.leaf 1088077110) (.leaf 1060852435)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1034418697) (.leaf 1008747602)) (.branch 55 (.leaf 983812103) (.leaf 959586335))) (.branch 58 (.branch 57 (.leaf 936045557) (.leaf 913166094)) (.branch 59 (.leaf 890925280) (.leaf 869301411))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 848273696) (.branch 62 (.leaf 827822208) (.leaf 807927848))) (.branch 65 (.branch 64 (.leaf 788572296) (.leaf 769737982)) (.branch 66 (.leaf 751408041) (.leaf 733566285)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 716197168) (.leaf 699285757)) (.branch 70 (.leaf 682817702) (.leaf 666779207))) (.branch 73 (.branch 72 (.leaf 651157008) (.leaf 635938346)) (.branch 74 (.leaf 621110943) (.leaf 606662982))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 592583085) (.branch 77 (.leaf 578860293) (.leaf 565484049))) (.branch 80 (.branch 79 (.leaf 552444177) (.leaf 539730868)) (.branch 81 (.leaf 527334663) (.leaf 515246437)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 503457387) (.leaf 491959015)) (.branch 85 (.leaf 480743115) (.leaf 469801766))) (.branch 88 (.branch 87 (.leaf 459127313) (.leaf 448712361)) (.branch 89 (.leaf 438549761) (.leaf 428632601)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 418954200) (.branch 92 (.leaf 409508090) (.leaf 400288018))) (.branch 95 (.branch 94 (.leaf 391287928) (.leaf 382501960)) (.branch 96 (.leaf 373924439) (.leaf 365549869)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 357372924) (.leaf 349388445)) (.branch 100 (.leaf 341591431) (.leaf 333977035))) (.branch 103 (.branch 102 (.leaf 326540554) (.leaf 319277430)) (.branch 104 (.leaf 312183240) (.leaf 305253693))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 298484623) (.leaf 291871988)) (.branch 108 (.leaf 285411864) (.leaf 279100439))) (.branch 111 (.branch 110 (.leaf 272934011) (.leaf 266908985)) (.branch 112 (.leaf 261021866) (.leaf 255269260)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 249647867) (.leaf 244154478)) (.branch 116 (.leaf 238785975) (.leaf 233539325))) (.branch 119 (.branch 118 (.leaf 228411579) (.leaf 223399865)) (.branch 120 (.leaf 218501394) (.leaf 213713449)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 176).q*(generalMeanRows 176).c/2-2 = (343/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable096.value]
    have hcontinuation : (generalMeanRows 176).q*(generalMeanRows 176).cutoff/2-2 = (1774/805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable094.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4817045131) (.branch 2 (.leaf 4640216643) (.leaf 4471712056))) (.branch 5 (.branch 4 (.leaf 4311042060) (.leaf 4157752366)) (.branch 6 (.leaf 4011420659) (.leaf 3871653863)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3738085701) (.leaf 3610374496)) (.branch 10 (.leaf 3488201197) (.leaf 3371267593))) (.branch 13 (.branch 12 (.leaf 3259294691) (.leaf 3152021257)) (.branch 14 (.leaf 3049202477) (.leaf 2950608749))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2856024568) (.branch 17 (.leaf 2765247521) (.leaf 2678087353))) (.branch 20 (.branch 19 (.leaf 2594365123) (.leaf 2513912417)) (.branch 21 (.leaf 2436570637) (.leaf 2362190333)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2290630597) (.leaf 2221758499)) (.branch 25 (.leaf 2155448567) (.leaf 2091582308))) (.branch 28 (.branch 27 (.leaf 2030047755) (.leaf 1970739063)) (.branch 29 (.leaf 1913556118) (.leaf 1858404186)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1805193576) (.branch 32 (.leaf 1753839340) (.leaf 1704260977))) (.branch 35 (.branch 34 (.leaf 1656382175) (.leaf 1610130552)) (.branch 36 (.leaf 1565437432) (.leaf 1522237623)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1480469217) (.leaf 1440073396)) (.branch 40 (.leaf 1400994260) (.leaf 1363178658))) (.branch 43 (.branch 42 (.leaf 1326576033) (.leaf 1291138274)) (.branch 44 (.leaf 1256819586) (.leaf 1223576354))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1191367029) (.branch 47 (.leaf 1160152012) (.leaf 1129893548))) (.branch 50 (.branch 49 (.leaf 1100555630) (.leaf 1072103900)) (.branch 51 (.leaf 1044505565) (.leaf 1017729313)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 991745237) (.leaf 966524757)) (.branch 55 (.leaf 942040556) (.leaf 918266513))) (.branch 58 (.branch 57 (.leaf 895177640) (.leaf 872750028)) (.branch 59 (.leaf 850960789) (.leaf 829788006))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 809210685) (.branch 62 (.leaf 789208709) (.leaf 769762793))) (.branch 65 (.branch 64 (.leaf 750854445) (.leaf 732465929)) (.branch 66 (.leaf 714580223) (.leaf 697180991)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 680252546) (.leaf 663779820)) (.branch 70 (.leaf 647748337) (.leaf 632144182))) (.branch 73 (.branch 72 (.leaf 616953977) (.leaf 602164856)) (.branch 74 (.leaf 587764442) (.leaf 573740820))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 560082526) (.branch 77 (.leaf 546778515) (.leaf 533818152))) (.branch 80 (.branch 79 (.leaf 521191188) (.leaf 508887744)) (.branch 81 (.leaf 496898297) (.leaf 485213663)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 473824982) (.leaf 462723705)) (.branch 85 (.leaf 451901579) (.leaf 441350637))) (.branch 88 (.branch 87 (.leaf 431063187) (.leaf 421031794)) (.branch 89 (.leaf 411249276) (.leaf 401708694)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 392403335) (.branch 92 (.leaf 383326710) (.leaf 374472542))) (.branch 95 (.branch 94 (.leaf 365834759) (.leaf 357407482)) (.branch 96 (.leaf 349185024) (.leaf 341161876)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 333332704) (.leaf 325692342)) (.branch 100 (.leaf 318235784) (.leaf 310958178))) (.branch 103 (.branch 102 (.leaf 303854823) (.leaf 296921161)) (.branch 104 (.leaf 290152770) (.leaf 283545363))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 277094782) (.leaf 270796991)) (.branch 108 (.leaf 264648074) (.leaf 258644229))) (.branch 111 (.branch 110 (.leaf 252781767) (.leaf 247057103)) (.branch 112 (.leaf 241466758) (.leaf 236007351)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 230675599) (.leaf 225468310)) (.branch 116 (.leaf 220382383) (.leaf 215414804))) (.branch 119 (.branch 118 (.leaf 210562643) (.leaf 205823051)) (.branch 120 (.leaf 201193257) (.leaf 196670566)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 177).q*(generalMeanRows 177).c/2-2 = (22/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable099.value]
    have hcontinuation : (generalMeanRows 177).q*(generalMeanRows 177).cutoff/2-2 = (1774/805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable094.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4890065040) (.branch 2 (.leaf 4713072779) (.leaf 4544361266))) (.branch 5 (.branch 4 (.leaf 4383444767) (.leaf 4229872288)) (.branch 6 (.leaf 4083224547) (.leaf 3943111264)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3809168740) (.leaf 3681057681)) (.branch 10 (.leaf 3558461232) (.leaf 3441083211))) (.branch 13 (.branch 12 (.leaf 3328646504) (.leaf 3220891611)) (.branch 14 (.leaf 3117575326) (.leaf 3018469532))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2923360101) (.branch 17 (.leaf 2832045895) (.leaf 2744337844))) (.branch 20 (.branch 19 (.leaf 2660058101) (.leaf 2579039271)) (.branch 21 (.leaf 2501123700) (.leaf 2426162814)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2354016520) (.leaf 2284552646)) (.branch 25 (.leaf 2217646423) (.leaf 2153180010))) (.branch 28 (.branch 27 (.leaf 2091042052) (.leaf 2031127267)) (.branch 29 (.leaf 1973336071) (.leaf 1917574219)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1863752478) (.branch 32 (.leaf 1811786326) (.leaf 1761595660))) (.branch 35 (.branch 34 (.leaf 1713104536) (.leaf 1666240920)) (.branch 36 (.leaf 1620936455) (.leaf 1577126252)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1534748680) (.leaf 1493745186)) (.branch 40 (.leaf 1454060112) (.leaf 1415640534))) (.branch 43 (.branch 42 (.leaf 1378436107) (.leaf 1342398922)) (.branch 44 (.leaf 1307483365) (.leaf 1273645996))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1240845427) (.branch 47 (.leaf 1209042207) (.leaf 1178198724))) (.branch 50 (.branch 49 (.leaf 1148279099) (.leaf 1119249097)) (.branch 51 (.leaf 1091076038) (.leaf 1063728716)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1037177321) (.leaf 1011393364)) (.branch 55 (.leaf 986349613) (.leaf 962020025))) (.branch 58 (.branch 57 (.leaf 938379685) (.leaf 915404749)) (.branch 59 (.leaf 893072393) (.leaf 871360756))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 850248896) (.branch 62 (.leaf 829716744) (.leaf 809745058))) (.branch 65 (.branch 64 (.leaf 790315388) (.leaf 771410031)) (.branch 66 (.leaf 753011999) (.leaf 735104985)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 717673327) (.leaf 700701982)) (.branch 70 (.leaf 684176491) (.leaf 668082958))) (.branch 73 (.branch 72 (.leaf 652408020) (.leaf 637138821)) (.branch 74 (.leaf 622262995) (.leaf 607768635))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 593644280) (.branch 77 (.leaf 579878891) (.leaf 566461832))) (.branch 80 (.branch 79 (.leaf 553382854) (.leaf 540632075)) (.branch 81 (.leaf 528199969) (.leaf 516077344)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 504255334) (.leaf 492725381)) (.branch 85 (.leaf 481479221) (.leaf 470508876))) (.branch 88 (.branch 87 (.leaf 459806639) (.leaf 449365063)) (.branch 89 (.leaf 439176949) (.leaf 429235341)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 419533508) (.branch 92 (.leaf 410064944) (.leaf 400823350))) (.branch 95 (.branch 94 (.leaf 391802634) (.leaf 382996895)) (.branch 96 (.leaf 374400424) (.leaf 366007687)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 357813328) (.leaf 349812154)) (.branch 100 (.leaf 341999134) (.leaf 334369390))) (.branch 103 (.branch 102 (.leaf 326918193) (.leaf 319640957)) (.branch 104 (.leaf 312533233) (.leaf 305590705))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 298809185) (.leaf 292184608)) (.branch 108 (.leaf 285713027) (.leaf 279390610))) (.branch 111 (.branch 110 (.leaf 273213635) (.leaf 267178488)) (.branch 112 (.leaf 261281657) (.leaf 255519730)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 249889389) (.leaf 244387410)) (.branch 116 (.leaf 239010661) (.leaf 233756093))) (.branch 119 (.branch 118 (.leaf 228620742) (.leaf 223601726)) (.branch 120 (.leaf 218696240) (.leaf 213901555)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 178).q*(generalMeanRows 178).c/2-2 = (343/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable096.value]
    have hcontinuation : (generalMeanRows 178).q*(generalMeanRows 178).cutoff/2-2 = (3538/1615:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable100.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4822576542) (.branch 2 (.leaf 4645600686) (.leaf 4476939050))) (.branch 5 (.branch 4 (.leaf 4316104119) (.leaf 4162643217)) (.branch 6 (.leaf 4016135470) (.leaf 3876189090)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3742438947) (.leaf 3614544389)) (.branch 10 (.leaf 3492187268) (.leaf 3375070175))) (.branch 13 (.branch 12 (.leaf 3262914823) (.leaf 3155460596)) (.branch 14 (.leaf 3052463223) (.leaf 2953693569))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2858936536) (.branch 17 (.leaf 2767990057) (.leaf 2680664172))) (.branch 20 (.branch 19 (.leaf 2596780186) (.leaf 2516169889)) (.branch 21 (.leaf 2438674848) (.leaf 2364145742)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2292441764) (.leaf 2223430054)) (.branch 25 (.leaf 2156985187) (.leaf 2092988692))) (.branch 28 (.branch 27 (.leaf 2031328607) (.leaf 1971899073)) (.branch 29 (.leaf 1914599948) (.leaf 1859336453)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1806018845) (.branch 32 (.leaf 1754562108) (.leaf 1704885670))) (.branch 35 (.branch 34 (.leaf 1656913133) (.leaf 1610572031)) (.branch 36 (.leaf 1565793591) (.leaf 1522512523)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1480666817) (.leaf 1440197550)) (.branch 40 (.leaf 1401048714) (.leaf 1363167049))) (.branch 43 (.branch 42 (.leaf 1326501886) (.leaf 1291005006)) (.branch 44 (.leaf 1256630500) (.leaf 1223334645))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1191075780) (.branch 47 (.leaf 1159814196) (.leaf 1129512033))) (.branch 50 (.branch 49 (.leaf 1100133173) (.leaf 1071643156)) (.branch 51 (.leaf 1044009085) (.leaf 1017199546)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 991184533) (.leaf 965935369)) (.branch 55 (.leaf 941424643) (.leaf 917626139))) (.branch 58 (.branch 57 (.leaf 894514782) (.leaf 872066573)) (.branch 59 (.leaf 850258540) (.leaf 829068684))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 808475929) (.branch 62 (.leaf 788460081) (.leaf 769001780))) (.branch 65 (.branch 64 (.leaf 750082463) (.leaf 731684321)) (.branch 66 (.leaf 713790266) (.leaf 696383896)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 679449461) (.leaf 662971832)) (.branch 70 (.leaf 646936475) (.leaf 631329418))) (.branch 73 (.branch 72 (.leaf 616137230) (.leaf 601346992)) (.branch 74 (.leaf 586946277) (.leaf 572923124))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 559266021) (.branch 77 (.leaf 545963881) (.leaf 533006025))) (.branch 80 (.branch 79 (.leaf 520382164) (.leaf 508082382)) (.branch 81 (.leaf 496097117) (.leaf 484417152)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 473033591) (.leaf 461937854)) (.branch 85 (.leaf 451121658) (.leaf 440577006))) (.branch 88 (.branch 87 (.leaf 430296178) (.leaf 420271713)) (.branch 89 (.leaf 410496405) (.leaf 400963288)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 391665628) (.branch 92 (.leaf 382596915) (.leaf 373750851))) (.branch 95 (.branch 94 (.leaf 365121343) (.leaf 356702496)) (.branch 96 (.leaf 348488603) (.leaf 340474140)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 332653757) (.leaf 325022273)) (.branch 100 (.leaf 317574668) (.leaf 310306077))) (.branch 103 (.branch 102 (.leaf 303211787) (.leaf 296287226)) (.branch 104 (.leaf 289527964) (.leaf 282929702))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 276488272) (.leaf 270199629)) (.branch 108 (.leaf 264059849) (.leaf 258065122))) (.branch 111 (.branch 110 (.leaf 252211750) (.leaf 246496142)) (.branch 112 (.leaf 240914813) (.leaf 235464375)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 230141540) (.leaf 224943109)) (.branch 116 (.leaf 219865979) (.leaf 214907130))) (.branch 119 (.branch 118 (.leaf 210063626) (.leaf 205332617)) (.branch 120 (.leaf 200711327) (.leaf 196197059)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 179).q*(generalMeanRows 179).c/2-2 = (22/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable099.value]
    have hcontinuation : (generalMeanRows 179).q*(generalMeanRows 179).cutoff/2-2 = (3538/1615:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable100.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4762097622) (.branch 2 (.leaf 4585033589) (.leaf 4416306395))) (.branch 5 (.branch 4 (.leaf 4255428534) (.leaf 4101947259)) (.branch 6 (.leaf 3955441544) (.leaf 3815519383)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3681815370) (.leaf 3553988517)) (.branch 10 (.leaf 3431720300) (.leaf 3314712888))) (.branch 13 (.branch 12 (.leaf 3202687537) (.leaf 3095383146)) (.branch 14 (.leaf 2992554929) (.leaf 2893973216))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2799422355) (.branch 17 (.leaf 2708699710) (.leaf 2621614740))) (.branch 20 (.branch 19 (.leaf 2537988162) (.leaf 2457651172)) (.branch 21 (.leaf 2380444734) (.leaf 2306218930)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2234832350) (.leaf 2166151536)) (.branch 25 (.leaf 2100050467) (.leaf 2036410082))) (.branch 28 (.branch 27 (.leaf 1975117837) (.leaf 1916067294)) (.branch 29 (.leaf 1859157741) (.leaf 1804293841)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1751385301) (.branch 32 (.leaf 1700346566) (.leaf 1651096533))) (.branch 35 (.branch 34 (.leaf 1603558288) (.leaf 1557658860)) (.branch 36 (.leaf 1513328982) (.leaf 1470502884)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1429118086) (.leaf 1389115210)) (.branch 40 (.leaf 1350437806) (.leaf 1313032182))) (.branch 43 (.branch 42 (.leaf 1276847254) (.leaf 1241834397)) (.branch 44 (.leaf 1207947312) (.leaf 1175141896))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1143376122) (.branch 47 (.leaf 1112609928) (.leaf 1082805111))) (.branch 50 (.branch 49 (.leaf 1053925227) (.leaf 1025935495)) (.branch 51 (.leaf 998802715) (.leaf 972495180)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 946982599) (.leaf 922236026)) (.branch 55 (.leaf 898227788) (.leaf 874931422))) (.branch 58 (.branch 57 (.leaf 852321610) (.leaf 830374128)) (.branch 59 (.leaf 809065782) (.leaf 788374365))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 768278602) (.branch 62 (.leaf 748758107) (.leaf 729793339))) (.branch 65 (.branch 64 (.leaf 711365561) (.leaf 693456800)) (.branch 66 (.leaf 676049813) (.leaf 659128047)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 642675614) (.leaf 626677251)) (.branch 70 (.leaf 611118297) (.leaf 595984662))) (.branch 73 (.branch 72 (.leaf 581262803) (.leaf 566939696)) (.branch 74 (.leaf 553002813) (.leaf 539440102))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 526239963) (.branch 77 (.leaf 513391226) (.leaf 500883139))) (.branch 80 (.branch 79 (.leaf 488705341) (.leaf 476847850)) (.branch 81 (.leaf 465301045) (.leaf 454055651)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 443102723) (.leaf 432433632)) (.branch 85 (.leaf 422040055) (.leaf 411913956))) (.branch 88 (.branch 87 (.leaf 402047578) (.leaf 392433432)) (.branch 89 (.leaf 383064283) (.leaf 373933142)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 365033255) (.branch 92 (.leaf 356358093) (.leaf 347901345))) (.branch 95 (.branch 94 (.leaf 339656907) (.leaf 331618874)) (.branch 96 (.leaf 323781535) (.leaf 316139362)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 308687004) (.leaf 301419280)) (.branch 100 (.leaf 294331176) (.leaf 287417831))) (.branch 103 (.branch 102 (.leaf 280674540) (.leaf 274096741)) (.branch 104 (.leaf 267680015) (.leaf 261420078))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 255312775) (.leaf 249354077)) (.branch 108 (.leaf 243540079) (.leaf 237866990))) (.branch 111 (.branch 110 (.leaf 232331132) (.leaf 226928938)) (.branch 112 (.leaf 221656943) (.leaf 216511786)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 211490201) (.leaf 206589019)) (.branch 116 (.leaf 201805161) (.leaf 197135635))) (.branch 119 (.branch 118 (.leaf 192577537) (.leaf 188128043)) (.branch 120 (.leaf 183784409) (.leaf 179543969)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 180).q*(generalMeanRows 180).c/2-2 = (361/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable083.value]
    have hcontinuation : (generalMeanRows 180).q*(generalMeanRows 180).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5303390712) (.branch 2 (.leaf 5134651650) (.leaf 4973606228))) (.branch 5 (.branch 4 (.leaf 4819795656) (.leaf 4672794428)) (.branch 6 (.leaf 4532207414) (.leaf 4397667257)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4268832044) (.leaf 4145383209)) (.branch 10 (.leaf 4027023647) (.leaf 3913476008))) (.branch 13 (.branch 12 (.leaf 3804481155) (.leaf 3699796761)) (.branch 14 (.leaf 3599196036) (.leaf 3502466572))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3409409279) (.branch 17 (.leaf 3319837420) (.leaf 3233575728))) (.branch 20 (.branch 19 (.leaf 3150459590) (.leaf 3070334305)) (.branch 21 (.leaf 2993054394) (.leaf 2918482974)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2846491176) (.leaf 2776957602)) (.branch 25 (.leaf 2709767838) (.leaf 2644813986))) (.branch 28 (.branch 27 (.leaf 2581994249) (.leaf 2521212531)) (.branch 29 (.leaf 2462378072) (.leaf 2405405116)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2350212588) (.branch 32 (.leaf 2296723807) (.leaf 2244866213))) (.branch 35 (.branch 34 (.leaf 2194571112) (.leaf 2145773443)) (.branch 36 (.leaf 2098411555) (.leaf 2052427002)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2007764355) (.leaf 1964371019)) (.branch 40 (.leaf 1922197068) (.leaf 1881195089))) (.branch 43 (.branch 42 (.leaf 1841320035) (.leaf 1802529086)) (.branch 44 (.leaf 1764781528) (.leaf 1728038626))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1692263512) (.branch 47 (.leaf 1657421086) (.leaf 1623477911))) (.branch 50 (.branch 49 (.leaf 1590402122) (.leaf 1558163340)) (.branch 51 (.leaf 1526732588) (.leaf 1496082219)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1466185837) (.leaf 1437018236)) (.branch 55 (.leaf 1408555332) (.leaf 1380774105))) (.branch 58 (.branch 57 (.leaf 1353652540) (.leaf 1327169579)) (.branch 59 (.leaf 1301305065) (.leaf 1276039699))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1251354996) (.branch 62 (.leaf 1227233240) (.leaf 1203657446))) (.branch 65 (.branch 64 (.leaf 1180611325) (.leaf 1158079245)) (.branch 66 (.leaf 1136046204) (.leaf 1114497791)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1093420162) (.leaf 1072800013)) (.branch 70 (.leaf 1052624549) (.leaf 1032881464))) (.branch 73 (.branch 72 (.leaf 1013558912) (.leaf 994645493)) (.branch 74 (.leaf 976130223) (.leaf 958002523))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 940252192) (.branch 77 (.leaf 922869396) (.leaf 905844648))) (.branch 80 (.branch 79 (.leaf 889168790) (.leaf 872832983)) (.branch 81 (.leaf 856828691) (.leaf 841147665)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 825781934) (.leaf 810723788)) (.branch 85 (.leaf 795965772) (.leaf 781500672))) (.branch 88 (.branch 87 (.leaf 767321506) (.leaf 753421511)) (.branch 89 (.leaf 739794138) (.leaf 726433042)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 713332071) (.branch 92 (.leaf 700485261) (.leaf 687886827))) (.branch 95 (.branch 94 (.leaf 675531157) (.leaf 663412802)) (.branch 96 (.leaf 651526475) (.leaf 639867039)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 628429505) (.leaf 617209023)) (.branch 100 (.leaf 606200882) (.leaf 595400498))) (.branch 103 (.branch 102 (.leaf 584803416) (.leaf 574405299)) (.branch 104 (.leaf 564201928) (.leaf 554189199))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 544363111) (.leaf 534719772)) (.branch 108 (.leaf 525255389) (.leaf 515966266))) (.branch 111 (.branch 110 (.leaf 506848804) (.leaf 497899491)) (.branch 112 (.leaf 489114905) (.leaf 480491708)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 472026645) (.leaf 463716539)) (.branch 116 (.leaf 455558292) (.leaf 447548877))) (.branch 119 (.branch 118 (.leaf 439685343) (.leaf 431964807)) (.branch 120 (.leaf 424384451) (.leaf 416941527)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 181).q*(generalMeanRows 181).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 181).q*(generalMeanRows 181).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable101.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5337464447) (.branch 2 (.leaf 5167641253) (.leaf 5005561132))) (.branch 5 (.branch 4 (.leaf 4850762343) (.leaf 4702816647)) (.branch 6 (.leaf 4561326376) (.leaf 4425921812)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4296258846) (.leaf 4172016865)) (.branch 10 (.leaf 4052896856) (.leaf 3938619685))) (.branch 13 (.branch 12 (.leaf 3828924552) (.leaf 3723567571)) (.branch 14 (.leaf 3622320497) (.leaf 3524969556))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3431314379) (.branch 17 (.leaf 3341167031) (.leaf 3254351117))) (.branch 20 (.branch 19 (.leaf 3170700966) (.leaf 3090060884)) (.branch 21 (.leaf 3012284457) (.leaf 2937233925)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2864779586) (.leaf 2794799267)) (.branch 25 (.leaf 2727177815) (.leaf 2661806641))) (.branch 28 (.branch 27 (.leaf 2598583294) (.leaf 2537411059)) (.branch 29 (.leaf 2478198596) (.leaf 2420859594)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2365312459) (.branch 32 (.leaf 2311480019) (.leaf 2259289245))) (.branch 35 (.branch 34 (.leaf 2208671004) (.leaf 2159559815)) (.branch 36 (.leaf 2111893631) (.leaf 2065613632)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2020664032) (.leaf 1976991899)) (.branch 40 (.leaf 1934546985) (.leaf 1893281572))) (.branch 43 (.branch 42 (.leaf 1853150325) (.leaf 1814110149)) (.branch 44 (.leaf 1776120066) (.leaf 1739141094))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1703136130) (.branch 47 (.leaf 1668069845) (.leaf 1633908588))) (.branch 50 (.branch 49 (.leaf 1600620291) (.leaf 1568174377)) (.branch 51 (.leaf 1536541686) (.leaf 1505694392)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1475605929) (.leaf 1446250929)) (.branch 55 (.leaf 1417605154) (.leaf 1389645435))) (.branch 58 (.branch 57 (.leaf 1362349617) (.leaf 1335696505)) (.branch 59 (.leaf 1309665815) (.leaf 1284238122))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1259394822) (.branch 62 (.leaf 1235118086) (.leaf 1211390820))) (.branch 65 (.branch 64 (.leaf 1188196630) (.leaf 1165519784)) (.branch 66 (.leaf 1143345183) (.leaf 1121658323)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1100445273) (.leaf 1079692642)) (.branch 70 (.leaf 1059387553) (.leaf 1039517620))) (.branch 73 (.branch 72 (.leaf 1020070923) (.leaf 1001035987)) (.branch 74 (.leaf 982401759) (.leaf 964157590))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 946293215) (.branch 77 (.leaf 928798737) (.leaf 911664605))) (.branch 80 (.branch 79 (.leaf 894881607) (.leaf 878440844)) (.branch 81 (.leaf 862333727) (.leaf 846551952)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 831087497) (.leaf 815932604)) (.branch 85 (.leaf 801079769) (.leaf 786521733))) (.branch 88 (.branch 87 (.leaf 772251467) (.leaf 758262166)) (.branch 89 (.leaf 744547239) (.leaf 731100299)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 717915155) (.branch 92 (.leaf 704985806) (.leaf 692306429))) (.branch 95 (.branch 94 (.leaf 679871374) (.leaf 667675161)) (.branch 96 (.leaf 655712465) (.leaf 643978119)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 632467099) (.leaf 621174527)) (.branch 100 (.leaf 610095659) (.leaf 599225884))) (.branch 103 (.branch 102 (.leaf 588560717) (.leaf 578095793)) (.branch 104 (.leaf 567826867) (.leaf 557749807))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 547860587) (.leaf 538155291)) (.branch 108 (.leaf 528630100) (.leaf 519281296))) (.branch 111 (.branch 110 (.leaf 510105255) (.leaf 501098443)) (.branch 112 (.leaf 492257417) (.leaf 483578817)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 475059367) (.leaf 466695870)) (.branch 116 (.leaf 458485206) (.leaf 450424332))) (.branch 119 (.branch 118 (.leaf 442510276) (.leaf 434740136)) (.branch 120 (.leaf 427111077) (.leaf 419620333)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 182).q*(generalMeanRows 182).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 182).q*(generalMeanRows 182).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable101.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4766641940) (.branch 2 (.leaf 4589273093) (.leaf 4420289029))) (.branch 5 (.branch 4 (.leaf 4259196986) (.leaf 4105539446)) (.branch 6 (.leaf 3958891060) (.leaf 3818855906)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3685065028) (.leaf 3557174227)) (.branch 10 (.leaf 3434862075) (.leaf 3317828115))) (.branch 13 (.branch 12 (.leaf 3205791236) (.leaf 3098488200)) (.branch 14 (.leaf 2995672298) (.leaf 2897112129))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2802590490) (.branch 17 (.leaf 2711903351) (.leaf 2624858928))) (.branch 20 (.branch 19 (.leaf 2541276824) (.leaf 2460987245)) (.branch 21 (.leaf 2383830278) (.leaf 2309655225)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2238319990) (.leaf 2169690513)) (.branch 25 (.leaf 2103640243) (.leaf 2040049662))) (.branch 28 (.branch 27 (.leaf 1978805826) (.leaf 1919801957)) (.branch 29 (.leaf 1862937055) (.leaf 1808115537)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1755246906) (.branch 32 (.leaf 1704245443) (.leaf 1655029912))) (.branch 35 (.branch 34 (.leaf 1607523298) (.leaf 1561652552)) (.branch 36 (.leaf 1517348357) (.leaf 1474544913)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1433179727) (.leaf 1393193429)) (.branch 40 (.leaf 1354529586) (.leaf 1317134541))) (.branch 43 (.branch 42 (.leaf 1280957254) (.leaf 1245949153)) (.branch 44 (.leaf 1212064002) (.leaf 1179257767))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1147488498) (.branch 47 (.leaf 1116716213) (.leaf 1086902793))) (.branch 50 (.branch 49 (.leaf 1058011881) (.leaf 1030008790)) (.branch 51 (.leaf 1002860410) (.leaf 976535127)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 951002747) (.leaf 926234418)) (.branch 55 (.leaf 902202561) (.leaf 878880808))) (.branch 58 (.branch 57 (.leaf 856243935) (.leaf 834267809)) (.branch 59 (.leaf 812929329) (.leaf 792206376))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 772077762) (.branch 62 (.leaf 752523188) (.leaf 733523198))) (.branch 65 (.branch 64 (.leaf 715059134) (.leaf 697113105)) (.branch 66 (.leaf 679667943) (.leaf 662707171)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 646214971) (.leaf 630176153)) (.branch 70 (.leaf 614576122) (.leaf 599400852))) (.branch 73 (.branch 72 (.leaf 584636864) (.leaf 570271192)) (.branch 74 (.leaf 556291368) (.leaf 542685394))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 529441721) (.branch 77 (.leaf 516549233) (.leaf 503997223))) (.branch 80 (.branch 79 (.leaf 491775378) (.leaf 479873758)) (.branch 81 (.leaf 468282786) (.leaf 456993224)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 445996166) (.leaf 435283018)) (.branch 85 (.leaf 424845490) (.leaf 414675579))) (.branch 88 (.branch 87 (.leaf 404765556) (.leaf 395107962)) (.branch 89 (.leaf 385695587) (.leaf 376521468)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 367578873) (.branch 92 (.leaf 358861296) (.leaf 350362446))) (.branch 95 (.branch 94 (.leaf 342076237) (.leaf 333996783)) (.branch 96 (.leaf 326118388) (.leaf 318435538)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 310942898) (.leaf 303635300)) (.branch 100 (.leaf 296507738) (.leaf 289555366))) (.branch 103 (.branch 102 (.leaf 282773486) (.leaf 276157545)) (.branch 104 (.leaf 269703132) (.leaf 263405968))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 257261906) (.leaf 251266924)) (.branch 108 (.leaf 245417117) (.leaf 239708701))) (.branch 111 (.branch 110 (.leaf 234138001) (.leaf 228701451)) (.branch 112 (.leaf 223395589) (.leaf 218217055)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 213162584) (.leaf 208229006)) (.branch 116 (.leaf 203413244) (.leaf 198712305))) (.branch 119 (.branch 118 (.leaf 194123282) (.leaf 189643352)) (.branch 120 (.leaf 185269768) (.leaf 180999861)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 183).q*(generalMeanRows 183).c/2-2 = (361/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable083.value]
    have hcontinuation : (generalMeanRows 183).q*(generalMeanRows 183).cutoff/2-2 = (1774/805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable094.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4798723570) (.branch 2 (.leaf 4620160952) (.leaf 4450039549))) (.branch 5 (.branch 4 (.leaf 4287863284) (.leaf 4133171560)) (.branch 6 (.leaf 3985536166) (.leaf 3844558513)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3709867162) (.leaf 3581115599)) (.branch 10 (.leaf 3457980231) (.leaf 3340158580))) (.branch 13 (.branch 12 (.leaf 3227367643) (.leaf 3119342410)) (.branch 14 (.leaf 3015834511) (.leaf 2916610988))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2821453176) (.branch 17 (.leaf 2730155672) (.leaf 2642525401))) (.branch 20 (.branch 19 (.leaf 2558380752) (.leaf 2477550788)) (.branch 21 (.leaf 2399874521) (.leaf 2325200237)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2253384884) (.leaf 2184293499)) (.branch 25 (.leaf 2117798682) (.leaf 2053780107))) (.branch 28 (.branch 27 (.leaf 1992124073) (.leaf 1932723082)) (.branch 29 (.leaf 1875475453) (.leaf 1820284962)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1767060502) (.branch 32 (.leaf 1715715776) (.leaf 1666169003))) (.branch 35 (.branch 34 (.leaf 1618342648) (.leaf 1572163171)) (.branch 36 (.leaf 1527560790) (.leaf 1484469259)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1442825667) (.leaf 1402570243)) (.branch 40 (.leaf 1363646175) (.leaf 1325999445))) (.branch 43 (.branch 42 (.leaf 1289578668) (.leaf 1254334948)) (.branch 44 (.leaf 1220221734) (.leaf 1187194699))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1155211608) (.branch 47 (.leaf 1124232212) (.leaf 1094218134))) (.branch 50 (.branch 49 (.leaf 1065132774) (.leaf 1036941209)) (.branch 51 (.leaf 1009610108) (.leaf 983107645)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 957403421) (.leaf 932468389)) (.branch 55 (.leaf 908274788) (.leaf 884796068))) (.branch 58 (.branch 57 (.leaf 862006840) (.leaf 839882804)) (.branch 59 (.leaf 818400707) (.leaf 797538278))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 777274190) (.branch 62 (.leaf 757588006) (.leaf 738460137))) (.branch 65 (.branch 64 (.leaf 719871802) (.leaf 701804988)) (.branch 66 (.leaf 684242412) (.leaf 667167486)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 650564287) (.leaf 634417520)) (.branch 70 (.leaf 618712493) (.leaf 603435088))) (.branch 73 (.branch 72 (.leaf 588571731) (.leaf 574109372)) (.branch 74 (.leaf 560035458) (.leaf 546337909))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 533005100) (.branch 77 (.leaf 520025840) (.leaf 507389350))) (.branch 80 (.branch 79 (.leaf 495085246) (.leaf 483103523)) (.branch 81 (.leaf 471434538) (.leaf 460068993)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 448997919) (.leaf 438212668)) (.branch 85 (.leaf 427704890) (.leaf 417466530))) (.branch 88 (.branch 87 (.leaf 407489809) (.leaf 397767215)) (.branch 89 (.leaf 388291491) (.leaf 379055625)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 370052843) (.branch 92 (.leaf 361276593) (.leaf 352720542))) (.branch 95 (.branch 94 (.leaf 344378563) (.leaf 336244731)) (.branch 96 (.leaf 328313310) (.leaf 320578752)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 313035683) (.leaf 305678901)) (.branch 100 (.leaf 298503368) (.leaf 291504203))) (.branch 103 (.branch 102 (.leaf 284676677) (.leaf 278016208)) (.branch 104 (.leaf 271518354) (.leaf 265178808))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 258993394) (.leaf 252958062)) (.branch 108 (.leaf 247068884) (.leaf 241322048))) (.branch 111 (.branch 110 (.leaf 235713854) (.leaf 230240714)) (.branch 112 (.leaf 224899141) (.leaf 219685753)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 214597263) (.leaf 209630481)) (.branch 116 (.leaf 204782306) (.leaf 200049727))) (.branch 119 (.branch 118 (.leaf 195429819) (.leaf 190919737)) (.branch 120 (.leaf 186516716) (.leaf 182218071)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 184).q*(generalMeanRows 184).c/2-2 = (361/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable083.value]
    have hcontinuation : (generalMeanRows 184).q*(generalMeanRows 184).cutoff/2-2 = (1774/805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable094.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5275569666) (.branch 2 (.leaf 5104932132) (.leaf 4942097500))) (.branch 5 (.branch 4 (.leaf 4786601141) (.leaf 4638012108)) (.branch 6 (.leaf 4495930185) (.leaf 4359983258)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4229824960) (.leaf 4105132544)) (.branch 10 (.leaf 3985604981) (.leaf 3870961231))) (.branch 13 (.branch 12 (.leaf 3760938681) (.leaf 3655291733)) (.branch 14 (.leaf 3553790509) (.leaf 3456219687))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3362377420) (.branch 17 (.leaf 3272074367) (.leaf 3185132793))) (.branch 20 (.branch 19 (.leaf 3101385749) (.leaf 3020676315)) (.branch 21 (.leaf 2942856912) (.leaf 2867788657)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2795340784) (.leaf 2725390089)) (.branch 25 (.leaf 2657820440) (.leaf 2592522305))) (.branch 28 (.branch 27 (.leaf 2529392326) (.leaf 2468332922)) (.branch 29 (.leaf 2409251916) (.leaf 2352062199)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2296681405) (.branch 32 (.leaf 2243031618) (.leaf 2191039099))) (.branch 35 (.branch 34 (.leaf 2140634026) (.leaf 2091750258)) (.branch 36 (.leaf 2044325110) (.leaf 1998299149)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1953615997) (.leaf 1910222152)) (.branch 40 (.leaf 1868066816) (.leaf 1827101741))) (.branch 43 (.branch 42 (.leaf 1787281080) (.leaf 1748561245)) (.branch 44 (.leaf 1710900782) (.leaf 1674260248))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1638602095) (.branch 47 (.leaf 1603890569) (.leaf 1570091604))) (.branch 50 (.branch 49 (.leaf 1537172731) (.leaf 1505102989)) (.branch 51 (.leaf 1473852844) (.leaf 1443394110)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1413699874) (.leaf 1384744433)) (.branch 55 (.leaf 1356503223) (.leaf 1328952762))) (.branch 58 (.branch 57 (.leaf 1302070593) (.leaf 1275835228)) (.branch 59 (.leaf 1250226100) (.leaf 1225223512))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1200808597) (.branch 62 (.leaf 1176963269) (.leaf 1153670190))) (.branch 65 (.branch 64 (.leaf 1130912728) (.leaf 1108674922)) (.branch 66 (.leaf 1086941450) (.leaf 1065697597)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1044929224) (.leaf 1024622740)) (.branch 70 (.leaf 1004765076) (.leaf 985343662))) (.branch 73 (.branch 72 (.leaf 966346397) (.leaf 947761635)) (.branch 74 (.leaf 929578156) (.leaf 911785149))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 894372196) (.branch 77 (.leaf 877329249) (.leaf 860646616))) (.branch 80 (.branch 79 (.leaf 844314942) (.leaf 828325198)) (.branch 81 (.leaf 812668665) (.leaf 797336915)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 782321808) (.leaf 767615471)) (.branch 85 (.leaf 753210290) (.leaf 739098899))) (.branch 88 (.branch 87 (.leaf 725274167) (.leaf 711729193)) (.branch 89 (.leaf 698457290) (.leaf 685451983)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 672706994) (.branch 92 (.leaf 660216237) (.leaf 647973810))) (.branch 95 (.branch 94 (.leaf 635973990) (.leaf 624211220)) (.branch 96 (.leaf 612680107) (.leaf 601375417)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 590292063) (.leaf 579425105)) (.branch 100 (.leaf 568769742) (.leaf 558321306))) (.branch 103 (.branch 102 (.leaf 548075260) (.leaf 538027189)) (.branch 104 (.leaf 528172801) (.leaf 518507916))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 509028469) (.leaf 499730499)) (.branch 108 (.leaf 490610151) (.leaf 481663669))) (.branch 111 (.branch 110 (.leaf 472887396) (.leaf 464277765)) (.branch 112 (.leaf 455831301) (.leaf 447544617)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 439414410) (.leaf 431437458)) (.branch 116 (.leaf 423610617) (.leaf 415930823))) (.branch 119 (.branch 118 (.leaf 408395082) (.leaf 401000475)) (.branch 120 (.leaf 393744150) (.leaf 386623325)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 185).q*(generalMeanRows 185).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    have hcontinuation : (generalMeanRows 185).q*(generalMeanRows 185).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable101.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5214876416) (.branch 2 (.leaf 5043464887) (.leaf 4879916141))) (.branch 5 (.branch 4 (.leaf 4723762612) (.leaf 4574570591)) (.branch 6 (.leaf 4431937269) (.leaf 4295488094)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4164874396) (.leaf 4039771258)) (.branch 10 (.leaf 3919875597) (.leaf 3804904430))) (.branch 13 (.branch 12 (.leaf 3694593305) (.leaf 3588694875)) (.branch 14 (.leaf 3486977605) (.leaf 3389224595))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3295232499) (.branch 17 (.leaf 3204810547) (.leaf 3117779640))) (.branch 20 (.branch 19 (.leaf 3033971530) (.leaf 2953228056)) (.branch 21 (.leaf 2875400452) (.leaf 2800348704)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2727940957) (.leaf 2658052972)) (.branch 25 (.leaf 2590567619) (.leaf 2525374414))) (.branch 28 (.branch 27 (.leaf 2462369084) (.leaf 2401453169)) (.branch 29 (.leaf 2342533651) (.leaf 2285522610)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2230336904) (.branch 32 (.leaf 2176897870) (.leaf 2125131049))) (.branch 35 (.branch 34 (.leaf 2074965929) (.leaf 2026335704)) (.branch 36 (.leaf 1979177051) (.leaf 1933429918)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1889037336) (.leaf 1845945230)) (.branch 40 (.leaf 1804102254) (.leaf 1763459629))) (.branch 43 (.branch 42 (.leaf 1723970996) (.leaf 1685592275)) (.branch 44 (.leaf 1648281538) (.leaf 1611998883))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1576706322) (.branch 47 (.leaf 1542367674) (.leaf 1508948462))) (.branch 50 (.branch 49 (.leaf 1476415822) (.leaf 1444738412)) (.branch 51 (.leaf 1413886328) (.leaf 1383831028)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1354545259) (.leaf 1326002983)) (.branch 55 (.leaf 1298179320) (.leaf 1271050480))) (.branch 58 (.branch 57 (.leaf 1244593707) (.leaf 1218787228)) (.branch 59 (.leaf 1193610198) (.leaf 1169042656))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1145065475) (.branch 62 (.leaf 1121660323) (.leaf 1098809623))) (.branch 65 (.branch 64 (.leaf 1076496511) (.leaf 1054704805)) (.branch 66 (.leaf 1033418968) (.leaf 1012624078)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 992305798) (.leaf 972450344)) (.branch 70 (.leaf 953044464) (.leaf 934075408))) (.branch 73 (.branch 72 (.leaf 915530906) (.leaf 897399144)) (.branch 74 (.leaf 879668745) (.leaf 862328746))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 845368580) (.branch 77 (.leaf 828778058) (.leaf 812547351))) (.branch 80 (.branch 79 (.leaf 796666977) (.leaf 781127778)) (.branch 81 (.leaf 765920915) (.leaf 751037845)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 736470316) (.leaf 722210348)) (.branch 85 (.leaf 708250225) (.leaf 694582483))) (.branch 88 (.branch 87 (.leaf 681199898) (.leaf 668095477)) (.branch 89 (.leaf 655262448) (.leaf 642694253)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 630384535) (.branch 92 (.leaf 618327133) (.leaf 606516074))) (.branch 95 (.branch 94 (.leaf 594945565) (.leaf 583609984)) (.branch 96 (.leaf 572503876) (.leaf 561621947)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 550959054) (.leaf 540510203)) (.branch 100 (.leaf 530270542) (.leaf 520235356))) (.branch 103 (.branch 102 (.leaf 510400061) (.leaf 500760200)) (.branch 104 (.leaf 491311438) (.leaf 482049559))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 472970460) (.leaf 464070146)) (.branch 108 (.leaf 455344732) (.leaf 446790431))) (.branch 111 (.branch 110 (.leaf 438403556) (.leaf 430180517)) (.branch 112 (.leaf 422117814) (.leaf 414212037)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 406459861) (.leaf 398858048)) (.branch 116 (.leaf 391403436) (.leaf 384092943))) (.branch 119 (.branch 118 (.leaf 376923564) (.leaf 369892364)) (.branch 120 (.leaf 362996483) (.leaf 356233126)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 186).q*(generalMeanRows 186).c/2-2 = (91/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable102.value]
    have hcontinuation : (generalMeanRows 186).q*(generalMeanRows 186).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable101.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5188746761) (.branch 2 (.leaf 5018128278) (.leaf 4855307283))) (.branch 5 (.branch 4 (.leaf 4699822468) (.leaf 4551245817)) (.branch 6 (.leaf 4409179698) (.leaf 4273254263)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4143125118) (.leaf 4018471232)) (.branch 10 (.leaf 3898993053) (.leaf 3784410803))) (.branch 13 (.branch 12 (.leaf 3674462938) (.leaf 3568904752)) (.branch 14 (.leaf 3467507104) (.leaf 3370055258))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3276347833) (.branch 17 (.leaf 3186195832) (.leaf 3099421763))) (.branch 20 (.branch 19 (.leaf 3015858823) (.leaf 2935350158)) (.branch 21 (.leaf 2857748178) (.leaf 2782913926)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2710716497) (.leaf 2641032502)) (.branch 25 (.leaf 2573745574) (.leaf 2508745907))) (.branch 28 (.branch 27 (.leaf 2445929837) (.leaf 2385199442)) (.branch 29 (.leaf 2326462181) (.leaf 2269630557)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2214621798) (.branch 32 (.leaf 2161357568) (.leaf 2109763694))) (.branch 35 (.branch 34 (.leaf 2059769911) (.leaf 2011309627)) (.branch 36 (.leaf 1964319700) (.leaf 1918740239)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1874514403) (.leaf 1831588228)) (.branch 40 (.leaf 1789910458) (.leaf 1749432386))) (.branch 43 (.branch 42 (.leaf 1710107710) (.leaf 1671892393)) (.branch 44 (.leaf 1634744538) (.leaf 1598624262))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1563493588) (.branch 47 (.leaf 1529316336) (.leaf 1496058025))) (.branch 50 (.branch 49 (.leaf 1463685777) (.leaf 1432168235)) (.branch 51 (.leaf 1401475472) (.leaf 1371578923)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1342451303) (.leaf 1314066547)) (.branch 55 (.leaf 1286399738) (.leaf 1259427052))) (.branch 58 (.branch 57 (.leaf 1233125699) (.leaf 1207473868)) (.branch 59 (.leaf 1182450677) (.leaf 1158036127))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1134211055) (.branch 62 (.leaf 1110957091) (.leaf 1088256622))) (.branch 65 (.branch 64 (.leaf 1066092749) (.leaf 1044449255)) (.branch 66 (.leaf 1023310569) (.leaf 1002661737)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 982488389) (.leaf 962776713)) (.branch 70 (.leaf 943513427) (.leaf 924685754))) (.branch 73 (.branch 72 (.leaf 906281397) (.leaf 888288519)) (.branch 74 (.leaf 870695720) (.leaf 853492013))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 836666814) (.branch 77 (.leaf 820209913) (.leaf 804111466))) (.branch 80 (.branch 79 (.leaf 788361973) (.leaf 772952264)) (.branch 81 (.leaf 757873484) (.leaf 743117082)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 728674793) (.leaf 714538629)) (.branch 85 (.leaf 700700867) (.leaf 687154036))) (.branch 88 (.branch 87 (.leaf 673890907) (.leaf 660904483)) (.branch 89 (.leaf 648187989) (.leaf 635734865)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 623538754) (.branch 92 (.leaf 611593494) (.leaf 599893114))) (.branch 95 (.branch 94 (.leaf 588431821) (.leaf 577203999)) (.branch 96 (.leaf 566204196) (.leaf 555427120)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 544867637) (.leaf 534520757)) (.branch 100 (.leaf 524381634) (.leaf 514445562))) (.branch 103 (.branch 102 (.leaf 504707964) (.leaf 495164391)) (.branch 104 (.leaf 485810519) (.leaf 476642139))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 467655160) (.leaf 458845597)) (.branch 108 (.leaf 450209575) (.leaf 441743319))) (.branch 111 (.branch 110 (.leaf 433443155) (.leaf 425305503)) (.branch 112 (.leaf 417326875) (.leaf 409503875)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 401833192) (.leaf 394311597)) (.branch 116 (.leaf 386935944) (.leaf 379703165))) (.branch 119 (.branch 118 (.leaf 372610266) (.leaf 365654329)) (.branch 120 (.leaf 358832505) (.leaf 352142015)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 187).q*(generalMeanRows 187).c/2-2 = (91/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable102.value]
    have hcontinuation : (generalMeanRows 187).q*(generalMeanRows 187).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5130520289) (.branch 2 (.leaf 4959155501) (.leaf 4795648281))) (.branch 5 (.branch 4 (.leaf 4639534314) (.leaf 4490382765)) (.branch 6 (.leaf 4347793349) (.leaf 4211393725)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4080837146) (.leaf 3955800365)) (.branch 10 (.leaf 3835981732) (.leaf 3721099485))) (.branch 13 (.branch 12 (.leaf 3610890203) (.leaf 3505107395)) (.branch 14 (.leaf 3403520229) (.leaf 3305912364))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3212080887) (.branch 17 (.leaf 3121835347) (.leaf 3034996865))) (.branch 20 (.branch 19 (.leaf 2951397316) (.leaf 2870878584)) (.branch 21 (.leaf 2793291874) (.leaf 2718497077)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646362188) (.leaf 2576762765)) (.branch 25 (.leaf 2509581432) (.leaf 2444707419))) (.branch 28 (.branch 27 (.leaf 2382036135) (.leaf 2321468771)) (.branch 29 (.leaf 2262911936) (.leaf 2206277316)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2151481356) (.branch 32 (.leaf 2098444968) (.leaf 2047093254))) (.branch 35 (.branch 34 (.leaf 1997355257) (.leaf 1949163716)) (.branch 36 (.leaf 1902454849) (.leaf 1857168145)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1813246172) (.leaf 1770634395)) (.branch 40 (.leaf 1729281006) (.leaf 1689136772))) (.branch 43 (.branch 42 (.leaf 1650154879) (.leaf 1612290803)) (.branch 44 (.leaf 1575502172) (.leaf 1539748651))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1504991824) (.branch 47 (.leaf 1471195090) (.leaf 1438323562))) (.branch 50 (.branch 49 (.leaf 1406343971) (.leaf 1375224581)) (.branch 51 (.leaf 1344935106) (.leaf 1315446628)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1286731527) (.leaf 1258763412)) (.branch 55 (.leaf 1231517056) (.leaf 1204968331))) (.branch 58 (.branch 57 (.leaf 1179094159) (.leaf 1153872448)) (.branch 59 (.leaf 1129282048) (.leaf 1105302700))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1081914993) (.branch 62 (.leaf 1059100316) (.leaf 1036840825))) (.branch 65 (.branch 64 (.leaf 1015119397) (.leaf 993919602)) (.branch 66 (.leaf 973225663) (.leaf 953022427)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 933295334) (.leaf 914030388)) (.branch 70 (.leaf 895214131) (.leaf 876833616))) (.branch 73 (.branch 72 (.leaf 858876383) (.leaf 841330439)) (.branch 74 (.leaf 824184232) (.leaf 807426633))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 791046917) (.branch 77 (.leaf 775034744) (.leaf 759380140))) (.branch 80 (.branch 79 (.leaf 744073483) (.leaf 729105486)) (.branch 81 (.leaf 714467183) (.leaf 700149913)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 686145310) (.leaf 672445288)) (.branch 85 (.leaf 659042028) (.leaf 645927970))) (.branch 88 (.branch 87 (.leaf 633095798) (.leaf 620538434)) (.branch 89 (.leaf 608249026) (.leaf 596220937)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 584447740) (.branch 92 (.leaf 572923206) (.leaf 561641299))) (.branch 95 (.branch 94 (.leaf 550596166) (.leaf 539782132)) (.branch 96 (.leaf 529193690) (.leaf 518825498)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 508672370) (.leaf 498729272)) (.branch 100 (.leaf 488991314) (.leaf 479453747))) (.branch 103 (.branch 102 (.leaf 470111956) (.leaf 460961457)) (.branch 104 (.leaf 451997890) (.leaf 443217017))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 434614714) (.leaf 426186972)) (.branch 108 (.leaf 417929887) (.leaf 409839663))) (.branch 111 (.branch 110 (.leaf 401912602) (.leaf 394145106)) (.branch 112 (.leaf 386533669) (.leaf 379074878)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 371765406) (.leaf 364602012)) (.branch 116 (.leaf 357581540) (.leaf 350700909))) (.branch 119 (.branch 118 (.leaf 343957118) (.leaf 337347240)) (.branch 120 (.leaf 330868422) (.leaf 324517878)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 188).q*(generalMeanRows 188).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 188).q*(generalMeanRows 188).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5209004653) (.branch 2 (.leaf 5037695233) (.leaf 4874200210))) (.branch 5 (.branch 4 (.leaf 4718058456) (.leaf 4568842067)) (.branch 6 (.leaf 4426153459) (.leaf 4289622775)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4158905565) (.leaf 4033680696)) (.branch 10 (.leaf 3913648474) (.leaf 3798528944))) (.branch 13 (.branch 12 (.leaf 3688060355) (.leaf 3581997766)) (.branch 14 (.leaf 3480111776) (.leaf 3382187374))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3288022881) (.branch 17 (.leaf 3197428992) (.leaf 3110227891))) (.branch 20 (.branch 19 (.leaf 3026252446) (.leaf 2945345462)) (.branch 21 (.leaf 2867359004) (.leaf 2792153766)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2719598490) (.leaf 2649569435)) (.branch 25 (.leaf 2581949879) (.leaf 2516629665))) (.branch 28 (.branch 27 (.leaf 2453504776) (.leaf 2392476943)) (.branch 29 (.leaf 2333453281) (.leaf 2276345950)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2221071844) (.branch 32 (.leaf 2167552297) (.leaf 2115712810))) (.branch 35 (.branch 34 (.leaf 2065482798) (.leaf 2016795356)) (.branch 36 (.leaf 1969587039) (.leaf 1923797653)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1879370066) (.leaf 1836250030)) (.branch 40 (.leaf 1794386009) (.leaf 1753729025))) (.branch 43 (.branch 42 (.leaf 1714232513) (.leaf 1675852179)) (.branch 44 (.leaf 1638545877) (.leaf 1602273483))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1566996783) (.branch 47 (.leaf 1532679372) (.leaf 1499286545))) (.branch 50 (.branch 49 (.leaf 1466785215) (.leaf 1435143813)) (.branch 51 (.leaf 1404332215) (.leaf 1374321661)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1345084679) (.leaf 1316595023)) (.branch 55 (.leaf 1288827603) (.leaf 1261758425))) (.branch 58 (.branch 57 (.leaf 1235364535) (.leaf 1209623967)) (.branch 59 (.leaf 1184515687) (.leaf 1160019550))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1136116253) (.branch 62 (.leaf 1112787290) (.leaf 1090014917))) (.branch 65 (.branch 64 (.leaf 1067782110) (.leaf 1046072531)) (.branch 66 (.leaf 1024870494) (.leaf 1004160930)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 983929364) (.leaf 964161880)) (.branch 70 (.leaf 944845097) (.leaf 925966140))) (.branch 73 (.branch 72 (.leaf 907512623) (.leaf 889472620)) (.branch 74 (.leaf 871834644) (.leaf 854587630))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 837720914) (.branch 77 (.leaf 821224212) (.leaf 805087607))) (.branch 80 (.branch 79 (.leaf 789301530) (.leaf 773856745)) (.branch 81 (.leaf 758744334) (.leaf 743955684)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 729482473) (.leaf 715316656)) (.branch 85 (.leaf 701450456) (.leaf 687876351))) (.branch 88 (.branch 87 (.leaf 674587062) (.leaf 661575546)) (.branch 89 (.leaf 648834981) (.leaf 636358765)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 624140498) (.branch 92 (.leaf 612173980) (.leaf 600453200))) (.branch 95 (.branch 94 (.leaf 588972330) (.leaf 577725718)) (.branch 96 (.leaf 566707878) (.leaf 555913488)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 545337380) (.leaf 534974537)) (.branch 100 (.leaf 524820086) (.leaf 514869290))) (.branch 103 (.branch 102 (.leaf 505117549) (.leaf 495560390)) (.branch 104 (.leaf 486193463) (.leaf 477012539))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 468013503) (.leaf 459192351)) (.branch 108 (.leaf 450545188) (.leaf 442068219))) (.branch 111 (.branch 110 (.leaf 433757752) (.leaf 425610190)) (.branch 112 (.leaf 417622029) (.leaf 409789857)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 402110347) (.leaf 394580257)) (.branch 116 (.leaf 387196425) (.leaf 379955771))) (.branch 119 (.branch 118 (.leaf 372855289) (.leaf 365892048)) (.branch 120 (.leaf 359063187) (.leaf 352365916)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 189).q*(generalMeanRows 189).c/2-2 = (91/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable102.value]
    have hcontinuation : (generalMeanRows 189).q*(generalMeanRows 189).cutoff/2-2 = (2174/981:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable104.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5134199136) (.branch 2 (.leaf 4962695767) (.leaf 4799041595))) (.branch 5 (.branch 4 (.leaf 4642773976) (.leaf 4493463569)) (.branch 6 (.leaf 4350711427) (.leaf 4214146395)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4083422786) (.leaf 3958218288)) (.branch 10 (.leaf 3838232080) (.leaf 3723183130))) (.branch 13 (.branch 12 (.leaf 3612808653) (.leaf 3506862720)) (.branch 14 (.leaf 3405114979) (.leaf 3307349509))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3213363753) (.branch 17 (.leaf 3122967564) (.leaf 3035982315))) (.branch 20 (.branch 19 (.leaf 2952240090) (.leaf 2871582944)) (.branch 21 (.leaf 2793862214) (.leaf 2718937893)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646678049) (.leaf 2576958285)) (.branch 25 (.leaf 2509661251) (.leaf 2444676180))) (.branch 28 (.branch 27 (.leaf 2381898466) (.leaf 2321229271)) (.branch 29 (.leaf 2262575160) (.leaf 2205847761)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2150963454) (.branch 32 (.leaf 2097843075) (.leaf 2046411641))) (.branch 35 (.branch 34 (.leaf 1996598104) (.leaf 1948335108)) (.branch 36 (.leaf 1901558770) (.leaf 1856208474)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1812226682) (.leaf 1769558746)) (.branch 40 (.leaf 1728152751) (.leaf 1687959348))) (.branch 43 (.branch 42 (.leaf 1648931613) (.leaf 1611024907)) (.branch 44 (.leaf 1574196746) (.leaf 1538406682))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1503616190) (.branch 47 (.leaf 1469788558) (.leaf 1436888790))) (.branch 50 (.branch 49 (.leaf 1404883512) (.leaf 1373740884)) (.branch 51 (.leaf 1343430516) (.leaf 1313923389)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1285191787) (.leaf 1257209221)) (.branch 55 (.leaf 1229950371) (.leaf 1203391021))) (.branch 58 (.branch 57 (.leaf 1177508001) (.leaf 1152279135)) (.branch 59 (.leaf 1127683191) (.leaf 1103699827))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1080309555) (.branch 62 (.leaf 1057493690) (.leaf 1035234312))) (.branch 65 (.branch 64 (.leaf 1013514231) (.leaf 992316947)) (.branch 66 (.leaf 971626619) (.leaf 951428029)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 931706558) (.leaf 912448152)) (.branch 70 (.leaf 893639295) (.leaf 875266987))) (.branch 73 (.branch 72 (.leaf 857318718) (.leaf 839782443)) (.branch 74 (.leaf 822646564) (.leaf 805899907))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 789531703) (.branch 77 (.leaf 773531569) (.leaf 757889493))) (.branch 80 (.branch 79 (.leaf 742595814) (.leaf 727641210)) (.branch 81 (.leaf 713016678) (.leaf 698713526)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 684723357) (.leaf 671038052)) (.branch 85 (.leaf 657649767) (.leaf 644550913))) (.branch 88 (.branch 87 (.leaf 631734149) (.leaf 619192372)) (.branch 89 (.leaf 606918706) (.leaf 594906494)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 583149287) (.branch 92 (.leaf 571640836) (.leaf 560375087))) (.branch 95 (.branch 94 (.leaf 549346170) (.leaf 538548391)) (.branch 96 (.leaf 527976229) (.leaf 517624326)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 507487484) (.leaf 497560653)) (.branch 100 (.leaf 487838933) (.leaf 478317562))) (.branch 103 (.branch 102 (.leaf 468991916) (.leaf 459857499)) (.branch 104 (.leaf 450909942) (.leaf 442144997))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 433558533) (.leaf 425146533)) (.branch 108 (.leaf 416905086) (.leaf 408830389))) (.branch 111 (.branch 110 (.leaf 400918738) (.leaf 393166528)) (.branch 112 (.leaf 385570250) (.leaf 378126485)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 370831901) (.leaf 363683255)) (.branch 116 (.leaf 356677384) (.leaf 349811206))) (.branch 119 (.branch 118 (.leaf 343081717) (.leaf 336485987)) (.branch 120 (.leaf 330021160) (.leaf 323684449)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 190).q*(generalMeanRows 190).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 190).q*(generalMeanRows 190).cutoff/2-2 = (2174/981:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable104.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5064697850) (.branch 2 (.leaf 4892911956) (.leaf 4729000743))) (.branch 5 (.branch 4 (.leaf 4572501710) (.leaf 4422985566)) (.branch 6 (.leaf 4280053325) (.leaf 4143333717)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4012480870) (.leaf 3887172227)) (.branch 10 (.leaf 3767106664) (.leaf 3652002799))) (.branch 13 (.branch 12 (.leaf 3541597454) (.leaf 3435644269)) (.branch 14 (.leaf 3333912430) (.leaf 3236185523))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3142260476) (.branch 17 (.leaf 3051946606) (.leaf 2965064732))) (.branch 20 (.branch 19 (.leaf 2881446372) (.leaf 2800933003)) (.branch 21 (.leaf 2723375377) (.leaf 2648632893)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2576573023) (.leaf 2507070774)) (.branch 25 (.leaf 2440008197) (.leaf 2375273926))) (.branch 28 (.branch 27 (.leaf 2312762764) (.leaf 2252375280)) (.branch 29 (.leaf 2194017456) (.leaf 2137600341)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2083039743) (.branch 32 (.leaf 2030255932) (.leaf 1979173372))) (.branch 35 (.branch 34 (.leaf 1929720468) (.leaf 1881829327)) (.branch 36 (.leaf 1835435539) (.leaf 1790477973)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1746898583) (.leaf 1704642229)) (.branch 40 (.leaf 1663656512) (.leaf 1623891611))) (.branch 43 (.branch 42 (.leaf 1585300142) (.leaf 1547837016)) (.branch 44 (.leaf 1511459313) (.leaf 1476126160))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1441798616) (.branch 47 (.leaf 1408439568) (.leaf 1376013630))) (.branch 50 (.branch 49 (.leaf 1344487047) (.leaf 1313827611)) (.branch 51 (.leaf 1284004575) (.leaf 1254988575)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1226751559) (.leaf 1199266715)) (.branch 55 (.leaf 1172508408) (.leaf 1146452119))) (.branch 58 (.branch 57 (.leaf 1121074384) (.leaf 1096352746)) (.branch 59 (.leaf 1072265697) (.leaf 1048792635))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1025913814) (.branch 62 (.leaf 1003610305) (.leaf 981863952))) (.branch 65 (.branch 64 (.leaf 960657338) (.leaf 939973745)) (.branch 66 (.leaf 919797119) (.leaf 900112042)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 880903701) (.leaf 862157853)) (.branch 70 (.leaf 843860805) (.leaf 825999385))) (.branch 73 (.branch 72 (.leaf 808560918) (.leaf 791533202)) (.branch 74 (.leaf 774904488) (.leaf 758663457))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 742799202) (.branch 77 (.leaf 727301209) (.leaf 712159339))) (.branch 80 (.branch 79 (.leaf 697363812) (.leaf 682905191)) (.branch 81 (.leaf 668774365) (.leaf 654962538)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 641461213) (.leaf 628262181)) (.branch 85 (.leaf 615357505) (.leaf 602739513))) (.branch 88 (.branch 87 (.leaf 590400787) (.leaf 578334146)) (.branch 89 (.leaf 566532645) (.leaf 554989558)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543698373) (.branch 92 (.leaf 532652785) (.leaf 521846681))) (.branch 95 (.branch 94 (.leaf 511274139) (.leaf 500929419)) (.branch 96 (.leaf 490806952) (.leaf 480901341)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 471207346) (.leaf 461719882)) (.branch 100 (.leaf 452434016) (.leaf 443344956))) (.branch 103 (.branch 102 (.leaf 434448049) (.leaf 425738774)) (.branch 104 (.leaf 417212740) (.leaf 408865678))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 400693440) (.leaf 392691992)) (.branch 108 (.leaf 384857409) (.leaf 377185876))) (.branch 111 (.branch 110 (.leaf 369673681) (.leaf 362317210)) (.branch 112 (.leaf 355112947) (.leaf 348057469)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341147442) (.leaf 334379621)) (.branch 116 (.leaf 327750844) (.leaf 321258031))) (.branch 119 (.branch 118 (.leaf 314898180) (.leaf 308668367)) (.branch 120 (.leaf 302565741) (.leaf 296587522)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 191).q*(generalMeanRows 191).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 191).q*(generalMeanRows 191).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5081452933) (.branch 2 (.leaf 4909098736) (.leaf 4744645270))) (.branch 5 (.branch 4 (.leaf 4587628505) (.leaf 4437617731)) (.branch 6 (.leaf 4294212639) (.leaf 4157040734)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4025754999) (.leaf 3900031809)) (.branch 10 (.leaf 3779569044) (.leaf 3664084390))) (.branch 13 (.branch 12 (.leaf 3553313802) (.leaf 3447010101)) (.branch 14 (.leaf 3344941712) (.leaf 3246891504))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3152655733) (.branch 17 (.leaf 3062043086) (.leaf 2974873788))) (.branch 20 (.branch 19 (.leaf 2890978802) (.leaf 2810199078)) (.branch 21 (.leaf 2732384874) (.leaf 2657395127)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2585096868) (.leaf 2515364691)) (.branch 25 (.leaf 2448080256) (.leaf 2383131831))) (.branch 28 (.branch 27 (.leaf 2320413868) (.leaf 2259826611)) (.branch 29 (.leaf 2201275726) (.leaf 2144671972)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2089930875) (.branch 32 (.leaf 2036972444) (.leaf 1985720893))) (.branch 35 (.branch 34 (.leaf 1936104388) (.leaf 1888054813)) (.branch 36 (.leaf 1841507545) (.leaf 1796401250)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1752677690) (.leaf 1710281544)) (.branch 40 (.leaf 1669160237) (.leaf 1629263785))) (.branch 43 (.branch 42 (.leaf 1590544647) (.leaf 1552957586)) (.branch 44 (.leaf 1516459538) (.leaf 1481009495))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1446568389) (.branch 47 (.leaf 1413098982) (.leaf 1380565772))) (.branch 50 (.branch 49 (.leaf 1348934892) (.leaf 1318174029)) (.branch 51 (.leaf 1288252332) (.leaf 1259140341)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1230809911) (.leaf 1203234141)) (.branch 55 (.leaf 1176387312) (.leaf 1150244823))) (.branch 58 (.branch 57 (.leaf 1124783134) (.leaf 1099979711)) (.branch 59 (.leaf 1075812977) (.leaf 1052262261))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1029307752) (.branch 62 (.leaf 1006930458) (.leaf 985112164))) (.branch 65 (.branch 64 (.leaf 963835394) (.leaf 943083375)) (.branch 66 (.leaf 922840001) (.leaf 903089802)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 883817915) (.leaf 865010052)) (.branch 70 (.leaf 846652474) (.leaf 828731964))) (.branch 73 (.branch 72 (.leaf 811235807) (.leaf 794151760)) (.branch 74 (.leaf 777468035) (.leaf 761173275))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 745256537) (.branch 77 (.leaf 729707274) (.leaf 714515312))) (.branch 80 (.branch 79 (.leaf 699670838) (.leaf 685164385)) (.branch 81 (.leaf 670986811) (.leaf 657129292)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643583302) (.leaf 630340604)) (.branch 85 (.leaf 617393236) (.leaf 604733502))) (.branch 88 (.branch 87 (.leaf 592353956) (.leaf 580247397)) (.branch 89 (.leaf 568406854) (.leaf 556825580)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 545497042) (.branch 92 (.leaf 534414912) (.leaf 523573059))) (.branch 95 (.branch 94 (.leaf 512965541) (.leaf 502586598)) (.branch 96 (.leaf 492430645) (.leaf 482492264)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472766198) (.leaf 463247348)) (.branch 100 (.leaf 453930763) (.leaf 444811634))) (.branch 103 (.branch 102 (.leaf 435885294) (.leaf 427147207)) (.branch 104 (.leaf 418592967) (.leaf 410218292))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402019018) (.leaf 393991099)) (.branch 108 (.leaf 386130598) (.leaf 378433686))) (.branch 111 (.branch 110 (.leaf 370896639) (.leaf 363515831)) (.branch 112 (.leaf 356287735) (.leaf 349208916)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342276029) (.leaf 335485819)) (.branch 116 (.leaf 328835113) (.leaf 322320820))) (.branch 119 (.branch 118 (.leaf 315939929) (.leaf 309689507)) (.branch 120 (.leaf 303566692) (.leaf 297568696)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 192).q*(generalMeanRows 192).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 192).q*(generalMeanRows 192).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5151052211) (.branch 2 (.leaf 4978985881) (.leaf 4814794511))) (.branch 5 (.branch 4 (.leaf 4658013942) (.leaf 4508213422)) (.branch 6 (.leaf 4364992693) (.leaf 4227979385)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4096826674) (.leaf 3971211191)) (.branch 10 (.leaf 3850831127) (.leaf 3735404527))) (.branch 13 (.branch 12 (.leaf 3624667745) (.leaf 3518374042)) (.branch 14 (.leaf 3416292313) (.leaf 3318205926))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3223911661) (.branch 17 (.leaf 3133218746) (.leaf 3045947966))) (.branch 20 (.branch 19 (.leaf 2961930857) (.leaf 2881008953)) (.branch 21 (.leaf 2803033103) (.leaf 2727862842)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2655365804) (.leaf 2585417184)) (.branch 25 (.leaf 2517899247) (.leaf 2452700861))) (.branch 28 (.branch 27 (.leaf 2389717078) (.leaf 2328848736)) (.branch 29 (.leaf 2270002092) (.leaf 2213088485)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2158024020) (.branch 32 (.leaf 2104729272) (.leaf 2053129014))) (.branch 35 (.branch 34 (.leaf 2003151963) (.leaf 1954730543)) (.branch 36 (.leaf 1907800661) (.leaf 1862301503)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1818175339) (.leaf 1775367346)) (.branch 40 (.leaf 1733825435) (.leaf 1693500096))) (.branch 43 (.branch 42 (.leaf 1654344252) (.leaf 1616313117)) (.branch 44 (.leaf 1579364067) (.leaf 1543456522))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1508551829) (.branch 47 (.leaf 1474613158) (.leaf 1441605396))) (.branch 50 (.branch 49 (.leaf 1409495061) (.leaf 1378250207)) (.branch 51 (.leaf 1347840344) (.leaf 1318236360)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1289410445) (.leaf 1261336027)) (.branch 55 (.leaf 1233987699) (.leaf 1207341168))) (.branch 58 (.branch 57 (.leaf 1181373186) (.leaf 1156061506)) (.branch 59 (.leaf 1131384825) (.leaf 1107322736))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1083855686) (.branch 62 (.leaf 1060964927) (.leaf 1038632482))) (.branch 65 (.branch 64 (.leaf 1016841105) (.leaf 995574241)) (.branch 66 (.leaf 974815996) (.leaf 954551104)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 934764897) (.leaf 915443274)) (.branch 70 (.leaf 896572677) (.leaf 878140062))) (.branch 73 (.branch 72 (.leaf 860132877) (.leaf 842539040)) (.branch 74 (.leaf 825346912) (.leaf 808545284))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 792123351) (.branch 77 (.leaf 776070697) (.leaf 760377275))) (.branch 80 (.branch 79 (.leaf 745033395) (.leaf 730029701)) (.branch 81 (.leaf 715357164) (.leaf 701007063)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 686970970) (.leaf 673240744)) (.branch 85 (.leaf 659808511) (.leaf 646666659))) (.branch 88 (.branch 87 (.leaf 633807824) (.leaf 621224879)) (.branch 89 (.leaf 608910925) (.leaf 596859283)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 585063482) (.branch 92 (.leaf 573517255) (.leaf 562214526))) (.branch 95 (.branch 94 (.leaf 551149406) (.leaf 540316183)) (.branch 96 (.leaf 529709318) (.leaf 519323435)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 509153318) (.leaf 499193902)) (.branch 100 (.leaf 489440271) (.leaf 479887646))) (.branch 103 (.branch 102 (.leaf 470531388) (.leaf 461366987)) (.branch 104 (.leaf 452390059) (.leaf 443596343))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 434981695) (.leaf 426542082)) (.branch 108 (.leaf 418273582) (.leaf 410172380))) (.branch 111 (.branch 110 (.leaf 402234759) (.leaf 394457102)) (.branch 112 (.leaf 386835890) (.leaf 379367690)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 372049162) (.leaf 364877050)) (.branch 116 (.leaf 357848182) (.leaf 350959466))) (.branch 119 (.branch 118 (.leaf 344207887) (.leaf 337590507)) (.branch 120 (.leaf 331104459) (.leaf 324746947)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 193).q*(generalMeanRows 193).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 193).q*(generalMeanRows 193).cutoff/2-2 = (2174/981:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable104.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5077558501) (.branch 2 (.leaf 4905337659) (.leaf 4741026368))) (.branch 5 (.branch 4 (.leaf 4584158910) (.leaf 4434303061)) (.branch 6 (.leaf 4291057162) (.leaf 4154047509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4022926013) (.leaf 3897368095)) (.branch 10 (.leaf 3777070790) (.leaf 3661751040))) (.branch 13 (.branch 12 (.leaf 3551144144) (.leaf 3445002351)) (.branch 14 (.leaf 3343093587) (.leaf 3245200287))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3151118339) (.branch 17 (.leaf 3060656112) (.leaf 2973633565))) (.branch 20 (.branch 19 (.leaf 2889881437) (.leaf 2809240500)) (.branch 21 (.leaf 2731560865) (.leaf 2656701355)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2584528921) (.leaf 2514918097)) (.branch 25 (.leaf 2447750510) (.leaf 2382914414))) (.branch 28 (.branch 27 (.leaf 2320304268) (.leaf 2259820335)) (.branch 29 (.leaf 2201368320) (.leaf 2144859028)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2090208045) (.branch 32 (.leaf 2037335450) (.leaf 1986165532))) (.branch 35 (.branch 34 (.leaf 1936626544) (.leaf 1888650458)) (.branch 36 (.leaf 1842172747) (.leaf 1797132176)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1753470610) (.leaf 1711132832)) (.branch 40 (.leaf 1670066374) (.leaf 1630221361))) (.branch 43 (.branch 42 (.leaf 1591550360) (.leaf 1554008243)) (.branch 44 (.leaf 1517552056) (.leaf 1482140900))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1447735814) (.branch 47 (.leaf 1414299668) (.leaf 1381797063))) (.branch 50 (.branch 49 (.leaf 1350194240) (.leaf 1319458984)) (.branch 51 (.leaf 1289560547) (.leaf 1260469567)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1232157996) (.leaf 1204599025)) (.branch 55 (.leaf 1177767029) (.leaf 1151637494))) (.branch 58 (.branch 57 (.leaf 1126186969) (.leaf 1101393004)) (.branch 59 (.leaf 1077234103) (.leaf 1053689676))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1030739988) (.branch 62 (.leaf 1008366122) (.leaf 986549935))) (.branch 65 (.branch 64 (.leaf 965274021) (.leaf 944521673)) (.branch 66 (.leaf 924276851) (.leaf 904524148)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 885248761) (.leaf 866436458)) (.branch 70 (.leaf 848073558) (.leaf 830146898))) (.branch 73 (.branch 72 (.leaf 812643812) (.leaf 795552108)) (.branch 74 (.leaf 778860044) (.leaf 762556309))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 746630005) (.branch 77 (.leaf 731070624) (.leaf 715868033))) (.branch 80 (.branch 79 (.leaf 701012458) (.leaf 686494467)) (.branch 81 (.leaf 672304953) (.leaf 658435124)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 644876487) (.leaf 631620834)) (.branch 85 (.leaf 618660234) (.leaf 605987015))) (.branch 88 (.branch 87 (.leaf 593593759) (.leaf 581473288)) (.branch 89 (.leaf 569618656) (.leaf 558023138)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 546680221) (.branch 92 (.leaf 535583598) (.leaf 524727157))) (.branch 95 (.branch 94 (.leaf 514104973) (.leaf 503711303)) (.branch 96 (.leaf 493540578) (.leaf 483587395)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 473846512) (.leaf 464312843)) (.branch 100 (.leaf 454981449) (.leaf 445847534))) (.branch 103 (.branch 102 (.leaf 436906441) (.leaf 428153645)) (.branch 104 (.leaf 419584749) (.leaf 411195482))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402981687) (.leaf 394939326)) (.branch 108 (.leaf 387064469) (.leaf 379353296))) (.branch 111 (.branch 110 (.leaf 371802088) (.leaf 364407225)) (.branch 112 (.leaf 357165185) (.leaf 350072538)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 343125946) (.leaf 336322155)) (.branch 116 (.leaf 329657998) (.leaf 323130387))) (.branch 119 (.branch 118 (.leaf 316736314) (.leaf 310472849)) (.branch 120 (.leaf 304337133) (.leaf 298326380)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 194).q*(generalMeanRows 194).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 194).q*(generalMeanRows 194).cutoff/2-2 = (2174/981:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable104.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5098263446) (.branch 2 (.leaf 4925339065) (.leaf 4760341552))) (.branch 5 (.branch 4 (.leaf 4602805343) (.leaf 4452298301)) (.branch 6 (.leaf 4308418796) (.leaf 4170793097)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4039073042) (.leaf 3912933933)) (.branch 10 (.leaf 3792072651) (.leaf 3676205951))) (.branch 13 (.branch 12 (.leaf 3565068910) (.leaf 3458413534)) (.branch 14 (.leaf 3356007482) (.leaf 3257632902))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3163085380) (.branch 17 (.leaf 3072172967) (.leaf 2984715295))) (.branch 20 (.branch 19 (.leaf 2900542766) (.leaf 2819495806)) (.branch 21 (.leaf 2741424177) (.leaf 2666186347)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2593648911) (.leaf 2523686045)) (.branch 25 (.leaf 2456179019) (.leaf 2391015731))) (.branch 28 (.branch 27 (.leaf 2328090284) (.leaf 2267302591)) (.branch 29 (.leaf 2208558009) (.leaf 2151766997)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2096844805) (.branch 32 (.leaf 2043711177) (.leaf 1992290075))) (.branch 35 (.branch 34 (.leaf 1942509428) (.leaf 1894300895)) (.branch 36 (.leaf 1847599638) (.leaf 1802344122)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1758475916) (.leaf 1715939514)) (.branch 40 (.leaf 1674682169) (.leaf 1634653732))) (.branch 43 (.branch 42 (.leaf 1595806503) (.leaf 1558095095)) (.branch 44 (.leaf 1521476304) (.leaf 1485908985))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1451353940) (.branch 47 (.leaf 1417773810) (.leaf 1385132973))) (.branch 50 (.branch 49 (.leaf 1353397452) (.leaf 1322534825)) (.branch 51 (.leaf 1292514141) (.leaf 1263305842)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1234881688) (.leaf 1207214692)) (.branch 55 (.leaf 1180279048) (.leaf 1154050074))) (.branch 58 (.branch 57 (.leaf 1128504153) (.leaf 1103618675)) (.branch 59 (.leaf 1079371993) (.leaf 1055743366))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1032712918) (.branch 62 (.leaf 1010261595) (.leaf 988371122))) (.branch 65 (.branch 64 (.leaf 967023964) (.leaf 946203293)) (.branch 66 (.leaf 925892949) (.leaf 906077413)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 886741770) (.leaf 867871687)) (.branch 70 (.leaf 849453378) (.leaf 831473584))) (.branch 73 (.branch 72 (.leaf 813919546) (.leaf 796778981)) (.branch 74 (.leaf 780040062) (.leaf 763691396))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 747722002) (.branch 77 (.leaf 732121299) (.leaf 716879078))) (.branch 80 (.branch 79 (.leaf 701985496) (.leaf 687431052)) (.branch 81 (.leaf 673206577) (.leaf 659303214)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 645712410) (.leaf 632425903)) (.branch 85 (.leaf 619435703) (.leaf 606734087))) (.branch 88 (.branch 87 (.leaf 594313587) (.leaf 582166977)) (.branch 89 (.leaf 570287263) (.leaf 558667675)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 547301660) (.branch 92 (.leaf 536182869) (.leaf 525305149))) (.branch 95 (.branch 94 (.leaf 514662539) (.leaf 504249260)) (.branch 96 (.leaf 494059709) (.leaf 484088449)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 474330208) (.leaf 464779868)) (.branch 100 (.leaf 455432461) (.leaf 446283164))) (.branch 103 (.branch 102 (.leaf 437327294) (.leaf 428560300)) (.branch 104 (.leaf 419977761) (.leaf 411575380))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403348982) (.leaf 395294504)) (.branch 108 (.leaf 387407999) (.leaf 379685624))) (.branch 111 (.branch 110 (.leaf 372123643) (.leaf 364718418)) (.branch 112 (.leaf 357466410) (.leaf 350364172)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 343408350) (.leaf 336595677)) (.branch 116 (.leaf 329922968) (.leaf 323387125))) (.branch 119 (.branch 118 (.leaf 316985125) (.leaf 310714025)) (.branch 120 (.leaf 304570954) (.leaf 298553116)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 195).q*(generalMeanRows 195).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 195).q*(generalMeanRows 195).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5026365757) (.branch 2 (.leaf 4853321261) (.leaf 4688238102))) (.branch 5 (.branch 4 (.leaf 4530649109) (.leaf 4380120620)) (.branch 6 (.leaf 4236249562) (.leaf 4098660834)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3967004964) (.leaf 3840956014)) (.branch 10 (.leaf 3720209677) (.leaf 3604481572))) (.branch 13 (.branch 12 (.leaf 3493505696) (.leaf 3387033017)) (.branch 14 (.leaf 3284830199) (.leaf 3186678440))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3092372412) (.branch 17 (.leaf 3001719289) (.leaf 2914537861))) (.branch 20 (.branch 19 (.leaf 2830657721) (.leaf 2749918516)) (.branch 21 (.leaf 2672169259) (.leaf 2597267699)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2525079734) (.leaf 2455478875)) (.branch 25 (.leaf 2388345746) (.leaf 2323567624))) (.branch 28 (.branch 27 (.leaf 2261038014) (.leaf 2200656252)) (.branch 29 (.leaf 2142327139) (.leaf 2085960597)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2031471359) (.branch 32 (.leaf 1978778668) (.leaf 1927806005))) (.branch 35 (.branch 34 (.leaf 1878480834) (.leaf 1830734365)) (.branch 36 (.leaf 1784501329) (.leaf 1739719770)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1696330855) (.leaf 1654278691)) (.branch 40 (.leaf 1613510154) (.leaf 1573974733))) (.branch 43 (.branch 42 (.leaf 1535624379) (.leaf 1498413369)) (.branch 44 (.leaf 1462298173) (.leaf 1427237333))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1393191349) (.branch 47 (.leaf 1360122570) (.leaf 1327995095))) (.branch 50 (.branch 49 (.leaf 1296774676) (.leaf 1266428631)) (.branch 51 (.leaf 1236925756) (.leaf 1208236254)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1180331651) (.leaf 1153184736)) (.branch 55 (.leaf 1126769488) (.leaf 1101061017))) (.branch 58 (.branch 57 (.leaf 1076035507) (.leaf 1051670159)) (.branch 59 (.leaf 1027943138) (.leaf 1004833528))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 982321285) (.branch 62 (.leaf 960387190) (.leaf 939012812))) (.branch 65 (.branch 64 (.leaf 918180466) (.leaf 897873181)) (.branch 66 (.leaf 878074660) (.leaf 858769250)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 839941914) (.leaf 821578194)) (.branch 70 (.leaf 803664192) (.leaf 786186538))) (.branch 73 (.branch 72 (.leaf 769132368) (.leaf 752489299)) (.branch 74 (.leaf 736245409) (.leaf 720389213))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 704909646) (.branch 77 (.leaf 689796041) (.leaf 675038116))) (.branch 80 (.branch 79 (.leaf 660625950) (.leaf 646549974)) (.branch 81 (.leaf 632800952) (.leaf 619369965)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 606248402) (.leaf 593427943)) (.branch 85 (.leaf 580900548) (.leaf 568658444))) (.branch 88 (.branch 87 (.leaf 556694116) (.leaf 545000296)) (.branch 89 (.leaf 533569951) (.leaf 522396273)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 511472673) (.branch 92 (.leaf 500792772) (.leaf 490350387))) (.branch 95 (.branch 94 (.leaf 480139530) (.leaf 470154398)) (.branch 96 (.leaf 460389365) (.leaf 450838975)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 441497937) (.leaf 432361117)) (.branch 100 (.leaf 423423534) (.leaf 414680353))) (.branch 103 (.branch 102 (.leaf 406126880) (.leaf 397758557)) (.branch 104 (.leaf 389570955) (.leaf 381559773))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 373720832) (.leaf 366050069)) (.branch 108 (.leaf 358543533) (.leaf 351197385))) (.branch 111 (.branch 110 (.leaf 344007890) (.leaf 336971415)) (.branch 112 (.leaf 330084424) (.leaf 323343479)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 316745231) (.leaf 310286421)) (.branch 116 (.leaf 303963876) (.leaf 297774506))) (.branch 119 (.branch 118 (.leaf 291715301) (.leaf 285783330)) (.branch 120 (.leaf 279975736) (.leaf 274289736)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 196).q*(generalMeanRows 196).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 196).q*(generalMeanRows 196).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5073424635) (.branch 2 (.leaf 4901350692) (.leaf 4737194382))) (.branch 5 (.branch 4 (.leaf 4580488331) (.leaf 4430798834)) (.branch 6 (.leaf 4287722911) (.leaf 4150885683)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4019938016) (.leaf 3894554405)) (.branch 10 (.leaf 3774431069) (.leaf 3659284231))) (.branch 13 (.branch 12 (.leaf 3548848560) (.leaf 3442875757)) (.branch 14 (.leaf 3341133272) (.leaf 3243403130))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3149480869) (.branch 17 (.leaf 3059174563) (.leaf 2972303925))) (.branch 20 (.branch 19 (.leaf 2888699490) (.leaf 2808201867)) (.branch 21 (.leaf 2730661038) (.leaf 2655935731)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2583892828) (.leaf 2514406822)) (.branch 25 (.leaf 2447359319) (.leaf 2382638575))) (.branch 28 (.branch 27 (.leaf 2320139065) (.leaf 2259761087)) (.branch 29 (.leaf 2201410393) (.leaf 2144997847)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2090439107) (.branch 32 (.leaf 2037654328) (.leaf 1986567888))) (.branch 35 (.branch 34 (.leaf 1937108132) (.leaf 1889207130)) (.branch 36 (.leaf 1842800459) (.leaf 1797826991)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1754228699) (.leaf 1711950478)) (.branch 40 (.leaf 1670939974) (.leaf 1631147425))) (.branch 43 (.branch 42 (.leaf 1592525513) (.leaf 1555029225)) (.branch 44 (.leaf 1518615720) (.leaf 1483244213))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1448875854) (.branch 47 (.leaf 1415473626) (.leaf 1383002239))) (.branch 50 (.branch 49 (.leaf 1351428040) (.leaf 1320718921)) (.branch 51 (.leaf 1290844237) (.leaf 1261774729)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1233482444) (.leaf 1205940674)) (.branch 55 (.leaf 1179123885) (.leaf 1153007656))) (.branch 58 (.branch 57 (.leaf 1127568625) (.leaf 1102784428)) (.branch 59 (.leaf 1078633654) (.leaf 1055095791))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1032151186) (.branch 62 (.leaf 1009780996) (.leaf 987967153))) (.branch 65 (.branch 64 (.leaf 966692321) (.leaf 945939861)) (.branch 66 (.leaf 925693800) (.leaf 905938794)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 886660099) (.leaf 867843545)) (.branch 70 (.leaf 849475506) (.leaf 831542872))) (.branch 73 (.branch 72 (.leaf 814033031) (.leaf 796933840)) (.branch 74 (.leaf 780233605) (.leaf 763921061))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 747985353) (.branch 77 (.leaf 732416015) (.leaf 717202955))) (.branch 80 (.branch 79 (.leaf 702336437) (.leaf 687807064)) (.branch 81 (.leaf 673605767) (.leaf 659723785)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 646152657) (.leaf 632884206)) (.branch 85 (.leaf 619910529) (.leaf 607223981))) (.branch 88 (.branch 87 (.leaf 594817171) (.leaf 582682946)) (.branch 89 (.leaf 570814382) (.leaf 559204776)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 547847639) (.branch 92 (.leaf 536736681) (.leaf 525865809))) (.branch 95 (.branch 94 (.leaf 515229117) (.leaf 504820879)) (.branch 96 (.leaf 494635542) (.leaf 484667717)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 474912178) (.leaf 465363850)) (.branch 100 (.leaf 456017807) (.leaf 446869267))) (.branch 103 (.branch 102 (.leaf 437913582) (.leaf 429146238)) (.branch 104 (.leaf 420562849) (.leaf 412159150))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403930995) (.leaf 395874353)) (.branch 108 (.leaf 387985303) (.leaf 380260029))) (.branch 111 (.branch 110 (.leaf 372694819) (.leaf 365286061)) (.branch 112 (.leaf 358030237) (.leaf 350923923)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 343963784) (.leaf 337146571)) (.branch 116 (.leaf 330469120) (.leaf 323928349))) (.branch 119 (.branch 118 (.leaf 317521251) (.leaf 311244898)) (.branch 120 (.leaf 305096436) (.leaf 299073080)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 197).q*(generalMeanRows 197).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 197).q*(generalMeanRows 197).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5017438056) (.branch 2 (.leaf 4844690902) (.leaf 4679921389))) (.branch 5 (.branch 4 (.leaf 4522659034) (.leaf 4372467217)) (.branch 6 (.leaf 4228940219) (.leaf 4091700582)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3960396744) (.leaf 3834700909)) (.branch 10 (.leaf 3714307133) (.leaf 3598929591))) (.branch 13 (.branch 12 (.leaf 3488301015) (.leaf 3382171268)) (.branch 14 (.leaf 3280306059) (.leaf 3182485760))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3088504336) (.branch 17 (.leaf 2998168364) (.leaf 2911296134))) (.branch 20 (.branch 19 (.leaf 2827716827) (.leaf 2747269756)) (.branch 21 (.leaf 2669803673) (.leaf 2595176127)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2523252877) (.leaf 2453907341)) (.branch 25 (.leaf 2387020099) (.leaf 2322478425))) (.branch 28 (.branch 27 (.leaf 2260175854) (.leaf 2200011784)) (.branch 29 (.leaf 2141891105) (.leaf 2085723857)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2031424906) (.branch 32 (.leaf 1978913649) (.leaf 1928113737))) (.branch 35 (.branch 34 (.leaf 1878952817) (.leaf 1831362291)) (.branch 36 (.leaf 1785277093) (.leaf 1740635478)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1697378829) (.leaf 1655451473)) (.branch 40 (.leaf 1614800510) (.leaf 1575375653))) (.branch 43 (.branch 42 (.leaf 1537129082) (.leaf 1500015300)) (.branch 44 (.leaf 1463991003) (.leaf 1429014958))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1395047889) (.branch 47 (.leaf 1362052364) (.leaf 1329992699))) (.branch 50 (.branch 49 (.leaf 1298834861) (.leaf 1268546377)) (.branch 51 (.leaf 1239096251) (.leaf 1210454885)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1182594005) (.leaf 1155486590)) (.branch 55 (.leaf 1129106807) (.leaf 1103429950))) (.branch 58 (.branch 57 (.leaf 1078432379) (.leaf 1054091467)) (.branch 59 (.leaf 1030385548) (.leaf 1007293868))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 984796538) (.branch 62 (.leaf 962874492) (.leaf 941509445))) (.branch 65 (.branch 64 (.leaf 920683856) (.leaf 900380888)) (.branch 66 (.leaf 880584376) (.leaf 861278796)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 842449231) (.leaf 824081343)) (.branch 70 (.leaf 806161344) (.leaf 788675975))) (.branch 73 (.branch 72 (.leaf 771612475) (.leaf 754958562)) (.branch 74 (.leaf 738702409) (.leaf 722832624))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 707338228) (.branch 77 (.leaf 692208640) (.leaf 677433658))) (.branch 80 (.branch 79 (.leaf 663003438) (.leaf 648908484)) (.branch 81 (.leaf 635139631) (.leaf 621688026)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 608545123) (.leaf 595702662)) (.branch 85 (.leaf 583152661) (.leaf 570887402))) (.branch 88 (.branch 87 (.leaf 558899424) (.leaf 547181507)) (.branch 89 (.leaf 535726665) (.leaf 524528137)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 513579375) (.branch 92 (.leaf 502874040) (.leaf 492405989))) (.branch 95 (.branch 94 (.leaf 482169270) (.leaf 472158114)) (.branch 96 (.leaf 462366925) (.leaf 452790281)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 443422918) (.leaf 434259729)) (.branch 100 (.leaf 425295760) (.leaf 416526199))) (.branch 103 (.branch 102 (.leaf 407946375) (.leaf 399551750)) (.branch 104 (.leaf 391337917) (.leaf 383300593))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 375435616) (.leaf 367738938)) (.branch 108 (.leaf 360206626) (.leaf 352834854))) (.branch 111 (.branch 110 (.leaf 345619899) (.leaf 338558141)) (.branch 112 (.leaf 331646056) (.leaf 324880215)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 318257279) (.leaf 311773999)) (.branch 116 (.leaf 305427210) (.leaf 299213828))) (.branch 119 (.branch 118 (.leaf 293130851) (.leaf 287175353)) (.branch 120 (.leaf 281344484) (.leaf 275635464)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 198).q*(generalMeanRows 198).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 198).q*(generalMeanRows 198).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4886997522) (.branch 2 (.leaf 4713822233) (.leaf 4548676009))) (.branch 5 (.branch 4 (.leaf 4391088366) (.leaf 4240622505)) (.branch 6 (.leaf 4096872379) (.leaf 3959460061)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3828033397) (.leaf 3702263892)) (.branch 10 (.leaf 3581844804) (.leaf 3466489429))) (.branch 13 (.branch 12 (.leaf 3355929546) (.leaf 3249914001)) (.branch 14 (.leaf 3148207432) (.leaf 3050589093))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2956851797) (.branch 17 (.leaf 2866800934) (.leaf 2780253585))) (.branch 20 (.branch 19 (.leaf 2697037700) (.leaf 2616991350)) (.branch 21 (.leaf 2539962037) (.leaf 2465806052)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2394387896) (.leaf 2325579736)) (.branch 25 (.leaf 2259260902) (.leaf 2195317428))) (.branch 28 (.branch 27 (.leaf 2133641621) (.leaf 2074131666)) (.branch 29 (.leaf 2016691253) (.leaf 1961229239)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1907659327) (.branch 32 (.leaf 1855899771) (.leaf 1805873100))) (.branch 35 (.branch 34 (.leaf 1757505861) (.leaf 1710728380)) (.branch 36 (.leaf 1665474535) (.leaf 1621681555)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1579289817) (.leaf 1538242668)) (.branch 40 (.leaf 1498486254) (.leaf 1459969361))) (.branch 43 (.branch 42 (.leaf 1422643264) (.leaf 1386461588)) (.branch 44 (.leaf 1351380177) (.leaf 1317356971))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1284351889) (.branch 47 (.leaf 1252326726) (.leaf 1221245043))) (.branch 50 (.branch 49 (.leaf 1191072079) (.leaf 1161774656)) (.branch 51 (.leaf 1133321099) (.leaf 1105681151)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1078825905) (.leaf 1052727727)) (.branch 55 (.leaf 1027360196) (.leaf 1002698036))) (.branch 58 (.branch 57 (.leaf 978717060) (.leaf 955394115)) (.branch 59 (.leaf 932707030) (.leaf 910634563))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 889156358) (.branch 62 (.leaf 868252903) (.leaf 847905481))) (.branch 65 (.branch 64 (.leaf 828096140) (.leaf 808807647)) (.branch 66 (.leaf 790023462) (.leaf 771727699)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 753905094) (.leaf 736540980)) (.branch 70 (.leaf 719621257) (.leaf 703132363))) (.branch 73 (.branch 72 (.leaf 687061253) (.leaf 671395373)) (.branch 74 (.leaf 656122637) (.leaf 641231408))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 626710474) (.branch 77 (.leaf 612549033) (.leaf 598736673))) (.branch 80 (.branch 79 (.leaf 585263353) (.leaf 572119391)) (.branch 81 (.leaf 559295445) (.leaf 546782496)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 534571842) (.leaf 522655076)) (.branch 85 (.leaf 511024080) (.leaf 499671008))) (.branch 88 (.branch 87 (.leaf 488588278) (.leaf 477768558)) (.branch 89 (.leaf 467204761) (.leaf 456890029)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 446817726) (.branch 92 (.leaf 436981431) (.leaf 427374928))) (.branch 95 (.branch 94 (.leaf 417992196) (.leaf 408827404)) (.branch 96 (.leaf 399874905) (.leaf 391129223)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 382585053) (.leaf 374237249)) (.branch 100 (.leaf 366080824) (.leaf 358110938))) (.branch 103 (.branch 102 (.leaf 350322897) (.leaf 342712144)) (.branch 104 (.leaf 335274258) (.leaf 328004946))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 320900040) (.leaf 313955490)) (.branch 108 (.leaf 307167365) (.leaf 300531843))) (.branch 111 (.branch 110 (.leaf 294045212) (.leaf 287703861)) (.branch 112 (.leaf 281504282) (.leaf 275443065)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 269516891) (.leaf 263722533)) (.branch 116 (.leaf 258056853) (.leaf 252516795))) (.branch 119 (.branch 118 (.leaf 247099389) (.leaf 241801740)) (.branch 120 (.leaf 236621033) (.leaf 231554526)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 199).q*(generalMeanRows 199).c/2-2 = (419/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable106.value]
    have hcontinuation : (generalMeanRows 199).q*(generalMeanRows 199).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4919385433) (.branch 2 (.leaf 4745062449) (.leaf 4578821741))) (.branch 5 (.branch 4 (.leaf 4420189707) (.leaf 4268726654)) (.branch 6 (.leaf 4124023843) (.leaf 3985700844)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3853403168) (.leaf 3726800142)) (.branch 10 (.leaf 3605582993) (.leaf 3489463117))) (.branch 13 (.branch 12 (.leaf 3378170513) (.leaf 3271452364)) (.branch 14 (.leaf 3169071748) (.leaf 3070806457))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2976447930) (.branch 17 (.leaf 2885800267) (.leaf 2798679337))) (.branch 20 (.branch 19 (.leaf 2714911950) (.leaf 2634335105)) (.branch 21 (.leaf 2556795290) (.leaf 2482147846)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2410256376) (.leaf 2340992199)) (.branch 25 (.leaf 2274233846) (.leaf 2209866596))) (.branch 28 (.branch 27 (.leaf 2147782041) (.leaf 2087877691)) (.branch 29 (.leaf 2030056600) (.leaf 1974227019)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1920302080) (.branch 32 (.leaf 1868199494) (.leaf 1817841279))) (.branch 35 (.branch 34 (.leaf 1769153492) (.leaf 1722065999)) (.branch 36 (.leaf 1676512241) (.leaf 1632429029)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1589756345) (.leaf 1548437162)) (.branch 40 (.leaf 1508417268) (.leaf 1469645110))) (.branch 43 (.branch 42 (.leaf 1432071639) (.leaf 1395650174)) (.branch 44 (.leaf 1360336265) (.leaf 1326087575))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1292863757) (.branch 47 (.leaf 1260626351) (.leaf 1229338679))) (.branch 50 (.branch 49 (.leaf 1198965747) (.leaf 1169474160)) (.branch 51 (.leaf 1140832030) (.leaf 1113008903)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1085975677) (.leaf 1059704537)) (.branch 55 (.leaf 1034168886) (.leaf 1009343281))) (.branch 58 (.branch 57 (.leaf 985203374) (.leaf 961725860)) (.branch 59 (.leaf 938888419) (.leaf 916669669))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 895049121) (.branch 62 (.leaf 874007131) (.leaf 853524859))) (.branch 65 (.branch 64 (.leaf 833584234) (.leaf 814167910)) (.branch 66 (.leaf 795259235) (.leaf 776842219)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 758901497) (.leaf 741422305)) (.branch 70 (.leaf 724390449) (.leaf 707792277))) (.branch 73 (.branch 72 (.leaf 691614658) (.leaf 675844955)) (.branch 74 (.leaf 660471001) (.leaf 645481082))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 630863912) (.branch 77 (.leaf 616608618) (.leaf 602704719))) (.branch 80 (.branch 79 (.leaf 589142107) (.leaf 575911035)) (.branch 81 (.leaf 563002099) (.leaf 550406223)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 538114644) (.leaf 526118902)) (.branch 85 (.leaf 514410823) (.leaf 502982510))) (.branch 88 (.branch 87 (.leaf 491826330) (.leaf 480934904)) (.branch 89 (.leaf 470301097) (.leaf 459918005)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 449778950) (.branch 92 (.leaf 439877466) (.leaf 430207297))) (.branch 95 (.branch 94 (.leaf 420762382) (.leaf 411536852)) (.branch 96 (.leaf 402525021) (.leaf 393721379)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385120583) (.leaf 376717456)) (.branch 100 (.leaf 368506975) (.leaf 360484270))) (.branch 103 (.branch 102 (.leaf 352644614) (.leaf 344983422)) (.branch 104 (.leaf 337496243) (.leaf 330178754))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323026761) (.leaf 316036188)) (.branch 108 (.leaf 309203075) (.leaf 302523577))) (.branch 111 (.branch 110 (.leaf 295993956) (.leaf 289610579)) (.branch 112 (.leaf 283369914) (.leaf 277268526)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271303077) (.leaf 265470318)) (.branch 116 (.leaf 259767089) (.leaf 254190316))) (.branch 119 (.branch 118 (.leaf 248737006) (.leaf 243404248)) (.branch 120 (.leaf 238189206) (.leaf 233089122)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 200).q*(generalMeanRows 200).c/2-2 = (419/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable106.value]
    have hcontinuation : (generalMeanRows 200).q*(generalMeanRows 200).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5007601100) (.branch 2 (.leaf 4835204395) (.leaf 4670798688))) (.branch 5 (.branch 4 (.leaf 4513910320) (.leaf 4364099839)) (.branch 6 (.leaf 4220959010) (.leaf 4084108141)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3953193696) (.leaf 3827886137)) (.branch 10 (.leaf 3707877990) (.leaf 3592882095))) (.branch 13 (.branch 12 (.leaf 3482630018) (.leaf 3376870618)) (.branch 14 (.leaf 3275368739) (.leaf 3177904018))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3084269801) (.branch 17 (.leaf 2994272148) (.leaf 2907728931))) (.branch 20 (.branch 19 (.leaf 2824468991) (.leaf 2744331382)) (.branch 21 (.leaf 2667164661) (.leaf 2592826246)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2521181816) (.leaf 2452104759)) (.branch 25 (.leaf 2385475666) (.leaf 2321181859))) (.branch 28 (.branch 27 (.leaf 2259116958) (.leaf 2199180470)) (.branch 29 (.leaf 2141277423) (.leaf 2085318013)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2031217285) (.branch 32 (.leaf 1978894828) (.leaf 1928274500))) (.branch 35 (.branch 34 (.leaf 1879284164) (.leaf 1831855450)) (.branch 36 (.leaf 1785923526) (.leaf 1741426887)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1698307158) (.leaf 1656508915)) (.branch 40 (.leaf 1615979504) (.leaf 1576668890))) (.branch 43 (.branch 42 (.leaf 1538529499) (.leaf 1501516082)) (.branch 44 (.leaf 1465585582) (.leaf 1430697007))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1396811322) (.branch 47 (.leaf 1363891331) (.leaf 1331901583))) (.branch 50 (.branch 49 (.leaf 1300808271) (.leaf 1270579146)) (.branch 51 (.leaf 1241183430) (.leaf 1212591739)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1184776006) (.leaf 1157709413)) (.branch 55 (.leaf 1131366323) (.leaf 1105722221))) (.branch 58 (.branch 57 (.leaf 1080753652) (.leaf 1056438170)) (.branch 59 (.leaf 1032754282) (.leaf 1009681403))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 987199806) (.branch 62 (.leaf 965290583) (.leaf 943935601))) (.branch 65 (.branch 64 (.leaf 923117463) (.leaf 902819475)) (.branch 66 (.leaf 883025609) (.leaf 863720468)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 844889262) (.leaf 826517774)) (.branch 70 (.leaf 808592332) (.leaf 791099787))) (.branch 73 (.branch 72 (.leaf 774027485) (.leaf 757363246)) (.branch 74 (.leaf 741095340) (.leaf 725212469))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 709703745) (.branch 77 (.leaf 694558670) (.leaf 679767125))) (.branch 80 (.branch 79 (.leaf 665319344) (.leaf 651205905)) (.branch 81 (.leaf 637417713) (.leaf 623945986)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 610782238) (.leaf 597918273)) (.branch 85 (.leaf 585346167) (.leaf 573058257))) (.branch 88 (.branch 87 (.leaf 561047135) (.leaf 549305631)) (.branch 89 (.leaf 537826807) (.leaf 526603945)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 515630543) (.branch 92 (.leaf 504900299) (.leaf 494407111))) (.branch 95 (.branch 94 (.leaf 484145061) (.leaf 474108414)) (.branch 96 (.leaf 464291609) (.leaf 454689252)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 445296108) (.leaf 436107099)) (.branch 100 (.leaf 427117293) (.leaf 418321904))) (.branch 103 (.branch 102 (.leaf 409716283) (.leaf 401295913)) (.branch 104 (.leaf 393056407) (.leaf 384993500))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 377103046) (.leaf 369381016)) (.branch 108 (.leaf 361823490) (.leaf 354426655))) (.branch 111 (.branch 110 (.leaf 347186802) (.leaf 340100324)) (.branch 112 (.leaf 333163706) (.leaf 326373531)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 319726469) (.leaf 313219278)) (.branch 116 (.leaf 306848802) (.leaf 300611965))) (.branch 119 (.branch 118 (.leaf 294505771) (.leaf 288527299)) (.branch 120 (.leaf 282673704) (.leaf 276942213)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 201).q*(generalMeanRows 201).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 201).q*(generalMeanRows 201).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable101.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5072154445) (.branch 2 (.leaf 4897535362) (.leaf 4731010289))) (.branch 5 (.branch 4 (.leaf 4572099461) (.leaf 4420357763)) (.branch 6 (.leaf 4275371695) (.leaf 4136756672)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4004154599) (.leaf 3877231692)) (.branch 10 (.leaf 3755676511) (.leaf 3639198195))) (.branch 13 (.branch 12 (.leaf 3527524851) (.leaf 3420402099)) (.branch 14 (.leaf 3317591752) (.leaf 3218870606))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3124029343) (.branch 17 (.leaf 3032871525) (.leaf 2945212673))) (.branch 20 (.branch 19 (.leaf 2860879423) (.leaf 2779708754)) (.branch 21 (.leaf 2701547272) (.leaf 2626250555)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2553682551) (.leaf 2483715017)) (.branch 25 (.leaf 2416227003) (.leaf 2351104381))) (.branch 28 (.branch 27 (.leaf 2288239396) (.leaf 2227530263)) (.branch 29 (.leaf 2168880783) (.leaf 2112199997)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2057401853) (.branch 32 (.leaf 2004404903) (.leaf 1953132025))) (.branch 35 (.branch 34 (.leaf 1903510151) (.leaf 1855470030)) (.branch 36 (.leaf 1808945994) (.leaf 1763875745)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1720200157) (.leaf 1677863090)) (.branch 40 (.leaf 1636811212) (.leaf 1596993841))) (.branch 43 (.branch 42 (.leaf 1558362793) (.leaf 1520872234)) (.branch 44 (.leaf 1484478551) (.leaf 1449140225))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1414817717) (.branch 47 (.leaf 1381473352) (.leaf 1349071221))) (.branch 50 (.branch 49 (.leaf 1317577083) (.leaf 1286958273)) (.branch 51 (.leaf 1257183615) (.leaf 1228223346)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1200049039) (.leaf 1172633528)) (.branch 55 (.leaf 1145950847) (.leaf 1119976165))) (.branch 58 (.branch 57 (.leaf 1094685725) (.leaf 1070056790)) (.branch 59 (.leaf 1046067592) (.leaf 1022697278))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 999925869) (.branch 62 (.leaf 977734213) (.leaf 956103942))) (.branch 65 (.branch 64 (.leaf 935017436) (.leaf 914457786)) (.branch 66 (.leaf 894408755) (.leaf 874854751)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 855780790) (.leaf 837172474)) (.branch 70 (.leaf 819015954) (.leaf 801297911))) (.branch 73 (.branch 72 (.leaf 784005529) (.leaf 767126470)) (.branch 74 (.leaf 750648853) (.leaf 734561235))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718852587) (.branch 77 (.leaf 703512276) (.leaf 688530051))) (.branch 80 (.branch 79 (.leaf 673896023) (.leaf 659600647)) (.branch 81 (.leaf 645634711) (.leaf 631989318)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618655876) (.leaf 605626080)) (.branch 85 (.leaf 592891906) (.leaf 580445592))) (.branch 88 (.branch 87 (.leaf 568279634) (.leaf 556386769)) (.branch 89 (.leaf 544759970) (.leaf 533392434)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522277573) (.branch 92 (.leaf 511409005) (.leaf 500780548))) (.branch 95 (.branch 94 (.leaf 490386209) (.leaf 480220180)) (.branch 96 (.leaf 470276826) (.leaf 460550684)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451036452) (.leaf 441728986)) (.branch 100 (.leaf 432623293) (.leaf 423714522))) (.branch 103 (.branch 102 (.leaf 414997965) (.leaf 406469048)) (.branch 104 (.leaf 398123325) (.leaf 389956479))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381964309) (.leaf 374142733)) (.branch 108 (.leaf 366487782) (.leaf 358995594))) (.branch 111 (.branch 110 (.leaf 351662412) (.leaf 344484581)) (.branch 112 (.leaf 337458543) (.leaf 330580835)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 323848085) (.leaf 317257010)) (.branch 116 (.leaf 310804412) (.leaf 304487175))) (.branch 119 (.branch 118 (.leaf 298302266) (.leaf 292246725)) (.branch 120 (.leaf 286317671) (.leaf 280512295)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 202).q*(generalMeanRows 202).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 202).q*(generalMeanRows 202).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable101.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5050176226) (.branch 2 (.leaf 4876301918) (.leaf 4710457303))) (.branch 5 (.branch 4 (.leaf 4552168831) (.leaf 4400997031)) (.branch 6 (.leaf 4256533536) (.leaf 4118398428)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3986237848) (.leaf 3859721863)) (.branch 10 (.leaf 3738542532) (.leaf 3622412166))) (.branch 13 (.branch 12 (.leaf 3511061752) (.leaf 3404239522)) (.branch 14 (.leaf 3301709655) (.leaf 3203251090))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3108656449) (.branch 17 (.leaf 3017731046) (.leaf 2930291985))) (.branch 20 (.branch 19 (.leaf 2846167333) (.leaf 2765195355)) (.branch 21 (.leaf 2687223815) (.leaf 2612109334)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2539716793) (.leaf 2469918786)) (.branch 25 (.leaf 2402595113) (.leaf 2337632313))) (.branch 28 (.branch 27 (.leaf 2274923225) (.leaf 2214366591)) (.branch 29 (.leaf 2155866683) (.leaf 2099332950)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2044679705) (.branch 32 (.leaf 1991825819) (.leaf 1940694444))) (.branch 35 (.branch 34 (.leaf 1891212755) (.leaf 1843311706)) (.branch 36 (.leaf 1796925808) (.leaf 1751992912)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1708454019) (.leaf 1666253091)) (.branch 40 (.leaf 1625336885) (.leaf 1585654786))) (.branch 43 (.branch 42 (.leaf 1547158661) (.leaf 1509802716)) (.branch 44 (.leaf 1473543365) (.leaf 1438339106))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1404150405) (.branch 47 (.leaf 1370939589) (.leaf 1338670739))) (.branch 50 (.branch 49 (.leaf 1307309600) (.leaf 1276823487)) (.branch 51 (.leaf 1247181202) (.leaf 1218352955)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1190310286) (.leaf 1163025998)) (.branch 55 (.leaf 1136474091) (.leaf 1110629695))) (.branch 58 (.branch 57 (.leaf 1085469018) (.leaf 1060969285)) (.branch 59 (.leaf 1037108688) (.leaf 1013866337))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 991222215) (.branch 62 (.leaf 969157130) (.leaf 947652679))) (.branch 65 (.branch 64 (.leaf 926691205) (.leaf 906255763)) (.branch 66 (.leaf 886330081) (.leaf 866898535)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 847946109) (.leaf 829458373)) (.branch 70 (.leaf 811421448) (.leaf 793821989))) (.branch 73 (.branch 72 (.leaf 776647152) (.leaf 759884575)) (.branch 74 (.leaf 743522352) (.leaf 727549018))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 711953523) (.branch 77 (.leaf 696725217) (.leaf 681853829))) (.branch 80 (.branch 79 (.leaf 667329454) (.leaf 653142533)) (.branch 81 (.leaf 639283839) (.leaf 625744465)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 612515806) (.leaf 599589549)) (.branch 85 (.leaf 586957660) (.leaf 574612373))) (.branch 88 (.branch 87 (.leaf 562546174) (.leaf 550751799)) (.branch 89 (.leaf 539222216) (.leaf 527950619)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 516930418) (.branch 92 (.leaf 506155232) (.leaf 495618878))) (.branch 95 (.branch 94 (.leaf 485315366) (.leaf 475238887)) (.branch 96 (.leaf 465383813) (.leaf 455744682)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 446316198) (.leaf 437093221)) (.branch 100 (.leaf 428070763) (.leaf 419243982))) (.branch 103 (.branch 102 (.leaf 410608175) (.leaf 402158777)) (.branch 104 (.leaf 393891349) (.leaf 385801583))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 377885287) (.leaf 370138390)) (.branch 108 (.leaf 362556930) (.leaf 355137058))) (.branch 111 (.branch 110 (.leaf 347875026) (.leaf 340767191)) (.branch 112 (.leaf 333810006) (.leaf 327000018)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 320333869) (.leaf 313808286)) (.branch 116 (.leaf 307420085) (.leaf 301166162))) (.branch 119 (.branch 118 (.leaf 295043494) (.leaf 289049137)) (.branch 120 (.leaf 283180222) (.leaf 277433952)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 203).q*(generalMeanRows 203).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 203).q*(generalMeanRows 203).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4994919280) (.branch 2 (.leaf 4820402359) (.leaf 4653975440))) (.branch 5 (.branch 4 (.leaf 4495161791) (.leaf 4343518961)) (.branch 6 (.leaf 4198635785) (.leaf 4060129707)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3927644389) (.leaf 3800847556)) (.branch 10 (.leaf 3679429056) (.leaf 3563099112))) (.branch 13 (.branch 12 (.leaf 3451586731) (.leaf 3344638273)) (.branch 14 (.leaf 3242016139) (.leaf 3143497582))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3048873619) (.branch 17 (.leaf 2957948044) (.leaf 2870536511))) (.branch 20 (.branch 19 (.leaf 2786465705) (.leaf 2705572576)) (.branch 21 (.leaf 2627703638) (.leaf 2552714313)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2480468342) (.leaf 2410837229)) (.branch 25 (.leaf 2343699735) (.leaf 2278941400))) (.branch 28 (.branch 27 (.leaf 2216454115) (.leaf 2156135712)) (.branch 29 (.leaf 2097889590) (.leaf 2041624366)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1987253554) (.branch 32 (.leaf 1934695260) (.leaf 1883871906))) (.branch 35 (.branch 34 (.leaf 1834709963) (.leaf 1787139713)) (.branch 36 (.leaf 1741095022) (.leaf 1696513122)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653334423) (.leaf 1611502317)) (.branch 40 (.leaf 1570963015) (.leaf 1531665379))) (.branch 43 (.branch 42 (.leaf 1493560774) (.leaf 1456602924)) (.branch 44 (.leaf 1420747781) (.leaf 1385953400))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1352179821) (.branch 47 (.leaf 1319388961) (.leaf 1287544512))) (.branch 50 (.branch 49 (.leaf 1256611841) (.leaf 1226557903)) (.branch 51 (.leaf 1197351154) (.leaf 1168961472)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1141360077) (.leaf 1114519470)) (.branch 55 (.leaf 1088413354) (.leaf 1063016581))) (.branch 58 (.branch 57 (.leaf 1038305089) (.leaf 1014255844)) (.branch 59 (.leaf 990846792) (.leaf 968056805))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 945865640) (.branch 62 (.leaf 924253887) (.leaf 903202935))) (.branch 65 (.branch 64 (.leaf 882694928) (.leaf 862712730)) (.branch 66 (.leaf 843239888) (.leaf 824260603)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 805759692) (.leaf 787722565)) (.branch 70 (.leaf 770135194) (.leaf 752984087))) (.branch 73 (.branch 72 (.leaf 736256261) (.leaf 719939223)) (.branch 74 (.leaf 704020943) (.leaf 688489834))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 673334732) (.branch 77 (.leaf 658544880) (.leaf 644109903))) (.branch 80 (.branch 79 (.leaf 630019799) (.leaf 616264914)) (.branch 81 (.leaf 602835937) (.leaf 589723873)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 576920042) (.leaf 564416055)) (.branch 85 (.leaf 552203807) (.leaf 540275466))) (.branch 88 (.branch 87 (.leaf 528623456) (.leaf 517240453)) (.branch 89 (.leaf 506119371) (.leaf 495253352)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 484635758) (.branch 92 (.leaf 474260163) (.leaf 464120341))) (.branch 95 (.branch 94 (.leaf 454210264) (.leaf 444524087)) (.branch 96 (.leaf 435056147) (.leaf 425800953)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 416753181) (.leaf 407907664)) (.branch 100 (.leaf 399259393) (.leaf 390803503))) (.branch 103 (.branch 102 (.leaf 382535273) (.leaf 374450121)) (.branch 104 (.leaf 366543596) (.leaf 358811373))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 351249254) (.leaf 343853155)) (.branch 108 (.leaf 336619111) (.leaf 329543264))) (.branch 111 (.branch 110 (.leaf 322621864) (.leaf 315851265)) (.branch 112 (.leaf 309227920) (.leaf 302748377)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 296409278) (.leaf 290207356)) (.branch 116 (.leaf 284139428) (.leaf 278202399))) (.branch 119 (.branch 118 (.leaf 272393253) (.leaf 266709052)) (.branch 120 (.leaf 261146937) (.leaf 255704120)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 204).q*(generalMeanRows 204).c/2-2 = (102/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable107.value]
    have hcontinuation : (generalMeanRows 204).q*(generalMeanRows 204).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4867452125) (.branch 2 (.leaf 4692538721) (.leaf 4525767863))) (.branch 5 (.branch 4 (.leaf 4366662658) (.leaf 4214780332)) (.branch 6 (.leaf 4069709250) (.leaf 3931066260)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3798494313) (.leaf 3671660319)) (.branch 10 (.leaf 3550253226) (.leaf 3433982276))) (.branch 13 (.branch 12 (.leaf 3322575432) (.leaf 3215777950)) (.branch 14 (.leaf 3113351080) (.leaf 3015070883))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2920727153) (.branch 17 (.leaf 2830122432) (.leaf 2743071104))) (.branch 20 (.branch 19 (.leaf 2659398569) (.leaf 2578940483)) (.branch 21 (.leaf 2501542057) (.leaf 2427057416)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2355349002) (.leaf 2286287027)) (.branch 25 (.leaf 2219748968) (.leaf 2155619097))) (.branch 28 (.branch 27 (.leaf 2093788047) (.leaf 2034152408)) (.branch 29 (.leaf 1976614357) (.leaf 1921081310)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1867465597) (.branch 32 (.leaf 1815684166) (.leaf 1765658300))) (.branch 35 (.branch 34 (.leaf 1717313359) (.leaf 1670578539)) (.branch 36 (.leaf 1625386640) (.leaf 1581673862)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1539379601) (.leaf 1498446268)) (.branch 40 (.leaf 1458819116) (.leaf 1420446078))) (.branch 43 (.branch 42 (.leaf 1383277613) (.leaf 1347266569)) (.branch 44 (.leaf 1312368048) (.leaf 1278539281))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1245739509) (.branch 47 (.leaf 1213929877) (.leaf 1183073330))) (.branch 50 (.branch 49 (.leaf 1153134514) (.leaf 1124079687)) (.branch 51 (.leaf 1095876632) (.leaf 1068494578)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1041904122) (.leaf 1016077159)) (.branch 55 (.leaf 990986818) (.leaf 966607390))) (.branch 58 (.branch 57 (.leaf 942914278) (.leaf 919883934)) (.branch 59 (.leaf 897493810) (.leaf 875722305))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 854548720) (.branch 62 (.leaf 833953211) (.leaf 813916751))) (.branch 65 (.branch 64 (.leaf 794421084) (.leaf 775448695)) (.branch 66 (.leaf 756982767) (.leaf 739007153)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 721506340) (.leaf 704465423)) (.branch 70 (.leaf 687870074) (.leaf 671706514))) (.branch 73 (.branch 72 (.leaf 655961492) (.leaf 640622255)) (.branch 74 (.leaf 625676531) (.leaf 611112501))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 596918784) (.branch 77 (.leaf 583084415) (.leaf 569598826))) (.branch 80 (.branch 79 (.leaf 556451831) (.leaf 543633605)) (.branch 81 (.leaf 531134673) (.leaf 518945892)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 507058436) (.leaf 495463787)) (.branch 85 (.leaf 484153716) (.leaf 473120276))) (.branch 88 (.branch 87 (.leaf 462355787) (.leaf 451852826)) (.branch 89 (.leaf 441604217) (.leaf 431603021)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 421842524) (.branch 92 (.leaf 412316231) (.leaf 403017858))) (.branch 95 (.branch 94 (.leaf 393941320) (.leaf 385080723)) (.branch 96 (.leaf 376430363) (.leaf 367984712)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 359738413) (.leaf 351686274)) (.branch 100 (.leaf 343823264) (.leaf 336144503))) (.branch 103 (.branch 102 (.leaf 328645259) (.leaf 321320940)) (.branch 104 (.leaf 314167094) (.leaf 307179397))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 300353653) (.leaf 293685791)) (.branch 108 (.leaf 287171855) (.leaf 280808003))) (.branch 111 (.branch 110 (.leaf 274590505) (.leaf 268515736)) (.branch 112 (.leaf 262580172) (.leaf 256780390)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 251113062) (.leaf 245574952)) (.branch 116 (.leaf 240162915) (.leaf 234873889))) (.branch 119 (.branch 118 (.leaf 229704899) (.leaf 224653050)) (.branch 120 (.leaf 219715523) (.leaf 214889578)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 205).q*(generalMeanRows 205).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 205).q*(generalMeanRows 205).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4816530706) (.branch 2 (.leaf 4641057998) (.leaf 4473787927))) (.branch 5 (.branch 4 (.leaf 4314240266) (.leaf 4161969115)) (.branch 6 (.leaf 4016559905) (.leaf 3877626725)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3744809930) (.leaf 3617773983)) (.branch 10 (.leaf 3496205525) (.leaf 3379811617))) (.branch 13 (.branch 12 (.leaf 3268318163) (.leaf 3161468469)) (.branch 14 (.leaf 3059021938) (.leaf 2960752882))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2866449435) (.branch 17 (.leaf 2775912564) (.leaf 2688955156))) (.branch 20 (.branch 19 (.leaf 2605401189) (.leaf 2525084968)) (.branch 21 (.leaf 2447850417) (.leaf 2373550436)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2302046300) (.leaf 2233207112)) (.branch 25 (.leaf 2166909289) (.leaf 2103036092))) (.branch 28 (.branch 27 (.leaf 2041477192) (.leaf 1982128261)) (.branch 29 (.leaf 1924890598) (.leaf 1869670781)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1816380342) (.branch 32 (.leaf 1764935464) (.leaf 1715256702))) (.branch 35 (.branch 34 (.leaf 1667268721) (.leaf 1620900048)) (.branch 36 (.leaf 1576082849) (.leaf 1532752716)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1490848464) (.leaf 1450311948)) (.branch 40 (.leaf 1411087892) (.leaf 1373123719))) (.branch 43 (.branch 42 (.leaf 1336369405) (.leaf 1300777336)) (.branch 44 (.leaf 1266302168) (.leaf 1232900710))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1200531799) (.branch 47 (.leaf 1169156194) (.leaf 1138736469))) (.branch 50 (.branch 49 (.leaf 1109236919) (.leaf 1080623464)) (.branch 51 (.leaf 1052863566) (.leaf 1025926146)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 999781510) (.leaf 974401272)) (.branch 55 (.leaf 949758293) (.leaf 925826612))) (.branch 58 (.branch 57 (.leaf 902581388) (.leaf 879998843)) (.branch 59 (.leaf 858056207) (.leaf 836731670))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 816004334) (.branch 62 (.leaf 795854166) (.leaf 776261955))) (.branch 65 (.branch 64 (.leaf 757209278) (.leaf 738678453)) (.branch 66 (.leaf 720652510) (.leaf 703115156)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 686050737) (.leaf 669444218)) (.branch 70 (.leaf 653281145) (.leaf 637547622))) (.branch 73 (.branch 72 (.leaf 622230286) (.leaf 607316279)) (.branch 74 (.leaf 592793229) (.leaf 578649224))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 564872797) (.branch 77 (.leaf 551452898) (.leaf 538378883))) (.branch 80 (.branch 79 (.leaf 525640494) (.leaf 513227837)) (.branch 81 (.leaf 501131375) (.leaf 489341905)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 477850548) (.leaf 466648734)) (.branch 85 (.leaf 455728189) (.leaf 445080921))) (.branch 88 (.branch 87 (.leaf 434699213) (.leaf 424575604)) (.branch 89 (.leaf 414702886) (.leaf 405074091)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 395682479) (.branch 92 (.leaf 386521530) (.leaf 377584940))) (.branch 95 (.branch 94 (.leaf 368866605) (.leaf 360360617)) (.branch 96 (.leaf 352061257) (.leaf 343962986)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 336060440) (.leaf 328348421)) (.branch 100 (.leaf 320821892) (.leaf 313475970))) (.branch 103 (.branch 102 (.leaf 306305924) (.leaf 299307162)) (.branch 104 (.leaf 292475235) (.leaf 285805825))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 279294742) (.leaf 272937920)) (.branch 108 (.leaf 266731413) (.leaf 260671391))) (.branch 111 (.branch 110 (.leaf 254754134) (.leaf 248976030)) (.branch 112 (.leaf 243333569) (.leaf 237823344)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 232442042) (.leaf 227186444)) (.branch 116 (.leaf 222053423) (.leaf 217039938))) (.branch 119 (.branch 118 (.leaf 212143031) (.leaf 207359828)) (.branch 120 (.leaf 202687533) (.leaf 198123426)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 206).q*(generalMeanRows 206).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 206).q*(generalMeanRows 206).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5027510517) (.branch 2 (.leaf 4851854895) (.leaf 4684342060))) (.branch 5 (.branch 4 (.leaf 4524492171) (.leaf 4371859891)) (.branch 6 (.leaf 4226031369) (.leaf 4086621556)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3953271788) (.leaf 3825647621)) (.branch 10 (.leaf 3703436880) (.leaf 3586347897))) (.branch 13 (.branch 12 (.leaf 3474107912) (.leaf 3366461629)) (.branch 14 (.leaf 3263169898) (.leaf 3164008519))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3068767147) (.branch 17 (.leaf 2977248293) (.leaf 2889266410))) (.branch 20 (.branch 19 (.leaf 2804647052) (.leaf 2723226106)) (.branch 21 (.leaf 2644849082) (.leaf 2569370461)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2496653094) (.leaf 2426567647)) (.branch 25 (.leaf 2358992089) (.leaf 2293811214))) (.branch 28 (.branch 27 (.leaf 2230916207) (.leaf 2170204234)) (.branch 29 (.leaf 2111578062) (.leaf 2054945715)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2000220140) (.branch 32 (.leaf 1947318910) (.leaf 1896163939))) (.branch 35 (.branch 34 (.leaf 1846681221) (.leaf 1798800581)) (.branch 36 (.leaf 1752455454) (.leaf 1707582663)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1664122227) (.leaf 1622017172)) (.branch 40 (.leaf 1581213356) (.leaf 1541659308))) (.branch 43 (.branch 42 (.leaf 1503306075) (.leaf 1466107080)) (.branch 44 (.leaf 1430017986) (.leaf 1394996576))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1361002628) (.branch 47 (.leaf 1327997812) (.leaf 1295945582))) (.branch 50 (.branch 49 (.leaf 1264811079) (.leaf 1234561043)) (.branch 51 (.leaf 1205163724) (.leaf 1176588802)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1148807312) (.leaf 1121791573)) (.branch 55 (.leaf 1095515118) (.leaf 1069952634))) (.branch 58 (.branch 57 (.leaf 1045079903) (.leaf 1020873739)) (.branch 59 (.leaf 997311946) (.leaf 974373258))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 952037297) (.branch 62 (.leaf 930284531) (.leaf 909096224))) (.branch 65 (.branch 64 (.leaf 888454405) (.leaf 868341825)) (.branch 66 (.leaf 848741926) (.leaf 829638802)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 811017175) (.leaf 792862358)) (.branch 70 (.leaf 775160232) (.leaf 757897216))) (.branch 73 (.branch 72 (.leaf 741060243) (.leaf 724636739)) (.branch 74 (.leaf 708614593) (.leaf 692982145))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 677728159) (.branch 77 (.leaf 662841804) (.leaf 648312642))) (.branch 80 (.branch 79 (.leaf 634130601) (.leaf 620285968)) (.branch 81 (.leaf 606769367) (.leaf 593571750)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 580684375) (.leaf 568098801)) (.branch 85 (.leaf 555806869) (.leaf 543800697))) (.branch 88 (.branch 87 (.leaf 532072659) (.leaf 520615384)) (.branch 89 (.leaf 509421738) (.leaf 498484819)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 487797947) (.branch 92 (.leaf 477354652) (.leaf 467148670))) (.branch 95 (.branch 94 (.leaf 457173930) (.leaf 447424552)) (.branch 96 (.leaf 437894835) (.leaf 428579252)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 419472444) (.leaf 410569212)) (.branch 100 (.leaf 401864511) (.leaf 393353448))) (.branch 103 (.branch 102 (.leaf 385031269) (.leaf 376893362)) (.branch 104 (.leaf 368935248) (.leaf 361152574))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 353541112) (.leaf 346096755)) (.branch 108 (.leaf 338815509) (.leaf 331693493))) (.branch 111 (.branch 110 (.leaf 324726932) (.leaf 317912156)) (.branch 112 (.leaf 311245594) (.leaf 304723773)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 298343312) (.leaf 292100923)) (.branch 116 (.leaf 285993403) (.leaf 280017636))) (.branch 119 (.branch 118 (.leaf 274170586) (.leaf 268449296)) (.branch 120 (.leaf 262850889) (.leaf 257372558)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 207).q*(generalMeanRows 207).c/2-2 = (102/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable107.value]
    have hcontinuation : (generalMeanRows 207).q*(generalMeanRows 207).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4972974092) (.branch 2 (.leaf 4796705723) (.leaf 4628640714))) (.branch 5 (.branch 4 (.leaf 4468295976) (.leaf 4315223124)) (.branch 6 (.leaf 4169005448) (.leaf 4029255207)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3895611202) (.leaf 3767736602)) (.branch 10 (.leaf 3645316975) (.leaf 3528058519))) (.branch 13 (.branch 12 (.leaf 3415686458) (.leaf 3307943585)) (.branch 14 (.leaf 3204588940) (.leaf 3105396604))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3010154600) (.branch 17 (.leaf 2918663890) (.leaf 2830737451))) (.branch 20 (.branch 19 (.leaf 2746199435) (.leaf 2664884392)) (.branch 21 (.leaf 2586636561) (.leaf 2511309209)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2438764029) (.leaf 2368870585)) (.branch 25 (.leaf 2301505789) (.leaf 2236553430))) (.branch 28 (.branch 27 (.leaf 2173903731) (.leaf 2113452938)) (.branch 29 (.leaf 2055102941) (.leaf 1998760919)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1944339019) (.branch 32 (.leaf 1891754042) (.leaf 1840927167))) (.branch 35 (.branch 34 (.leaf 1791783680) (.leaf 1744252734)) (.branch 36 (.leaf 1698267115) (.leaf 1653763029)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1610679899) (.leaf 1568960184)) (.branch 40 (.leaf 1528549197) (.leaf 1489394944))) (.branch 43 (.branch 42 (.leaf 1451447974) (.leaf 1414661229)) (.branch 44 (.leaf 1378989914) (.leaf 1344391370))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1310824956) (.branch 47 (.leaf 1278251935) (.leaf 1246635375))) (.branch 50 (.branch 49 (.leaf 1215940046) (.leaf 1186132332)) (.branch 51 (.leaf 1157180143) (.leaf 1129052833)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1101721124) (.leaf 1075157035)) (.branch 55 (.leaf 1049333814) (.leaf 1024225875))) (.branch 58 (.branch 57 (.leaf 999808734) (.leaf 976058958)) (.branch 59 (.leaf 952954107) (.leaf 930472689))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 908594106) (.branch 62 (.leaf 887298613) (.leaf 866567278))) (.branch 65 (.branch 64 (.leaf 846381935) (.leaf 826725155)) (.branch 66 (.leaf 807580204) (.leaf 788931011)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 770762138) (.leaf 753058749)) (.branch 70 (.leaf 735806579) (.leaf 718991911))) (.branch 73 (.branch 72 (.leaf 702601549) (.leaf 686622793)) (.branch 74 (.leaf 671043417) (.leaf 655851648))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 641036143) (.branch 77 (.leaf 626585973) (.leaf 612490603))) (.branch 80 (.branch 79 (.leaf 598739873) (.leaf 585323984)) (.branch 81 (.leaf 572233481) (.leaf 559459239)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 546992446) (.leaf 534824594)) (.branch 85 (.leaf 522947463) (.leaf 511353109))) (.branch 88 (.branch 87 (.leaf 500033854) (.leaf 488982274)) (.branch 89 (.leaf 478191188) (.leaf 467653651)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 457362939) (.branch 92 (.leaf 447312547) (.leaf 437496174))) (.branch 95 (.branch 94 (.leaf 427907719) (.leaf 418541271)) (.branch 96 (.leaf 409391105) (.leaf 400451668)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 391717580) (.leaf 383183623)) (.branch 100 (.leaf 374844737) (.leaf 366696011))) (.branch 103 (.branch 102 (.leaf 358732683) (.leaf 350950129)) (.branch 104 (.leaf 343343860) (.leaf 335909518))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 328642871) (.leaf 321539807)) (.branch 108 (.leaf 314596333) (.leaf 307808566))) (.branch 111 (.branch 110 (.leaf 301172734) (.leaf 294685171)) (.branch 112 (.leaf 288342309) (.leaf 282140681)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 276076915) (.leaf 270147730)) (.branch 116 (.leaf 264349933) (.leaf 258680418))) (.branch 119 (.branch 118 (.leaf 253136161) (.leaf 247714219)) (.branch 120 (.leaf 242411727) (.leaf 237225894)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 208).q*(generalMeanRows 208).c/2-2 = (419/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable106.value]
    have hcontinuation : (generalMeanRows 208).q*(generalMeanRows 208).cutoff/2-2 = (1090/489:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable103.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4848451608) (.branch 2 (.leaf 4671815979) (.leaf 4503437348))) (.branch 5 (.branch 4 (.leaf 4342832307) (.leaf 4189552000)) (.branch 6 (.leaf 4043179109) (.leaf 3903325169)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3769628148) (.leaf 3641750288)) (.branch 10 (.leaf 3519376151) (.leaf 3402210859))) (.branch 13 (.branch 12 (.leaf 3289978497) (.leaf 3182420671)) (.branch 14 (.leaf 3079295190) (.leaf 2980374869))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2885446439) (.branch 17 (.leaf 2794309547) (.leaf 2706775840))) (.branch 20 (.branch 19 (.leaf 2622668131) (.leaf 2541819625)) (.branch 21 (.leaf 2464073213) (.leaf 2389280818)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2317302799) (.leaf 2248007389)) (.branch 25 (.leaf 2181270186) (.leaf 2116973678))) (.branch 28 (.branch 27 (.leaf 2055006805) (.leaf 1995264546)) (.branch 29 (.leaf 1937647549) (.leaf 1882061770)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1828418155) (.branch 32 (.leaf 1776632334) (.leaf 1726624333))) (.branch 35 (.branch 34 (.leaf 1678318318) (.leaf 1631642342)) (.branch 36 (.leaf 1586528124) (.leaf 1542910826)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1500728859) (.leaf 1459923694)) (.branch 40 (.leaf 1420439685) (.leaf 1382223909))) (.branch 43 (.branch 42 (.leaf 1345226012) (.leaf 1309398061)) (.branch 44 (.leaf 1274694414) (.leaf 1241071592))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1208488160) (.branch 47 (.leaf 1176904617) (.leaf 1146283290))) (.branch 50 (.branch 49 (.leaf 1116588236) (.leaf 1087785149)) (.branch 51 (.leaf 1059841276) (.leaf 1032725332)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1006407426) (.leaf 980858984)) (.branch 55 (.leaf 956052687) (.leaf 931962402))) (.branch 58 (.branch 57 (.leaf 908563124) (.leaf 885830915)) (.branch 59 (.leaf 863742858) (.leaf 842276996))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 821412292) (.branch 62 (.leaf 801128581) (.leaf 781406526))) (.branch 65 (.branch 64 (.leaf 762227579) (.leaf 743573944)) (.branch 66 (.leaf 725428537) (.leaf 707774956)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 690597445) (.leaf 673880869)) (.branch 70 (.leaf 657610677) (.leaf 641772882))) (.branch 73 (.branch 72 (.leaf 626354032) (.leaf 611341185)) (.branch 74 (.leaf 596721885) (.leaf 582484143))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 568616414) (.branch 77 (.leaf 555107577) (.leaf 541946916))) (.branch 80 (.branch 79 (.leaf 529124104) (.leaf 516629185)) (.branch 81 (.leaf 504452555) (.leaf 492584951)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 481017437) (.leaf 469741385)) (.branch 85 (.leaf 458748465) (.leaf 448030635))) (.branch 88 (.branch 87 (.leaf 437580122) (.leaf 427389421)) (.branch 89 (.leaf 417451273) (.leaf 407758665)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 398304810) (.branch 92 (.leaf 389083149) (.leaf 380087333))) (.branch 95 (.branch 94 (.leaf 371311218) (.leaf 362748858)) (.branch 96 (.leaf 354394495) (.leaf 346242554)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 338287635) (.leaf 330524506)) (.branch 100 (.leaf 322948095) (.leaf 315553490))) (.branch 103 (.branch 102 (.leaf 308335924) (.leaf 301290780)) (.branch 104 (.leaf 294413575) (.leaf 287699964))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 281145729) (.leaf 274746779)) (.branch 108 (.leaf 268499139) (.leaf 262398955))) (.branch 111 (.branch 110 (.leaf 256442482) (.leaf 250626084)) (.branch 112 (.leaf 244946229) (.leaf 239399486)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 233982520) (.leaf 228692091)) (.branch 116 (.leaf 223525052) (.leaf 218478340))) (.branch 119 (.branch 118 (.leaf 213548980) (.leaf 208734077)) (.branch 120 (.leaf 204030817) (.leaf 199436462)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 209).q*(generalMeanRows 209).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 209).q*(generalMeanRows 209).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable098.value]
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
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
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
