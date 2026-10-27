import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block12
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block14
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 630. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0630
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5359332376) (.branch 2 (.leaf 5182618691) (.leaf 5013738022))) (.branch 5 (.branch 4 (.leaf 4852242714) (.leaf 4697716816)) (.branch 6 (.leaf 4549773309) (.leaf 4408051637)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4272215499) (.leaf 4141950858)) (.branch 10 (.leaf 4016964163) (.leaf 3896980732))) (.branch 13 (.branch 12 (.leaf 3781743294) (.leaf 3671010670)) (.branch 14 (.leaf 3564556571) (.leaf 3462168503))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3363646773) (.branch 17 (.leaf 3268803572) (.leaf 3177462146))) (.branch 20 (.branch 19 (.leaf 3089456028) (.leaf 3004628338)) (.branch 21 (.leaf 2922831130) (.leaf 2843924806)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2767777560) (.leaf 2694264875)) (.branch 25 (.leaf 2623269052) (.leaf 2554678776))) (.branch 28 (.branch 27 (.leaf 2488388717) (.leaf 2424299156)) (.branch 29 (.leaf 2362315636) (.leaf 2302348645)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2244313311) (.branch 32 (.leaf 2188129131) (.leaf 2133719705))) (.branch 35 (.branch 34 (.leaf 2081012495) (.leaf 2029938605)) (.branch 36 (.leaf 1980432561) (.leaf 1932432120)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1885878086) (.leaf 1840714133)) (.branch 40 (.leaf 1796886648) (.leaf 1754344578))) (.branch 43 (.branch 42 (.leaf 1713039288) (.leaf 1672924428)) (.branch 44 (.leaf 1633955809) (.leaf 1596091286))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1559290646) (.branch 47 (.leaf 1523515506) (.leaf 1488729218))) (.branch 50 (.branch 49 (.leaf 1454896772) (.leaf 1421984717)) (.branch 51 (.leaf 1389961072) (.leaf 1358795258)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1328458018) (.leaf 1298921357)) (.branch 55 (.leaf 1270158474) (.leaf 1242143698))) (.branch 58 (.branch 57 (.leaf 1214852441) (.leaf 1188261136)) (.branch 59 (.leaf 1162347188) (.leaf 1137088929))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1112465571) (.branch 62 (.leaf 1088457161) (.leaf 1065044545))) (.branch 65 (.branch 64 (.leaf 1042209328) (.leaf 1019933835)) (.branch 66 (.leaf 998201081) (.leaf 976994738)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 956299100) (.leaf 936099060)) (.branch 70 (.leaf 916380080) (.leaf 897128162))) (.branch 73 (.branch 72 (.leaf 878329827) (.leaf 859972093)) (.branch 74 (.leaf 842042447) (.leaf 824528829))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 807419609) (.branch 77 (.leaf 790703571) (.leaf 774369892))) (.branch 80 (.branch 79 (.leaf 758408127) (.leaf 742808190)) (.branch 81 (.leaf 727560343) (.leaf 712655177)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 698083600) (.leaf 683836823)) (.branch 85 (.leaf 669906350) (.leaf 656283961))) (.branch 88 (.branch 87 (.leaf 642961706) (.leaf 629931889)) (.branch 89 (.leaf 617187063) (.leaf 604720013)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 592523757) (.branch 92 (.leaf 580591525) (.leaf 568916760))) (.branch 95 (.branch 94 (.leaf 557493104) (.leaf 546314395)) (.branch 96 (.leaf 535374655) (.leaf 524668086)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 514189061) (.leaf 503932120)) (.branch 100 (.leaf 493891962) (.leaf 484063440))) (.branch 103 (.branch 102 (.leaf 474441555) (.leaf 465021451)) (.branch 104 (.leaf 455798410) (.leaf 446767845))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 437925300) (.leaf 429266438)) (.branch 108 (.leaf 420787047) (.leaf 412483024))) (.branch 111 (.branch 110 (.leaf 404350383) (.leaf 396385241)) (.branch 112 (.leaf 388583820) (.leaf 380942444)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 373457532) (.leaf 366125597)) (.branch 116 (.leaf 358943244) (.leaf 351907164))) (.branch 119 (.branch 118 (.leaf 345014135) (.leaf 338261015)) (.branch 120 (.leaf 331644744) (.leaf 325162337)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 630).q*(generalMeanRows 630).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 630).q*(generalMeanRows 630).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5581926282) (.branch 2 (.leaf 5403257658) (.leaf 5232455186))) (.branch 5 (.branch 4 (.leaf 5069068359) (.leaf 4912678632)) (.branch 6 (.leaf 4762896635) (.leaf 4619359676)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4481729515) (.leaf 4349690360)) (.branch 10 (.leaf 4222947066) (.leaf 4101223511))) (.branch 13 (.branch 12 (.leaf 3984261121) (.leaf 3871817540)) (.branch 14 (.leaf 3763665418) (.leaf 3659591306))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3559394652) (.branch 17 (.leaf 3462886880) (.leaf 3369890550))) (.branch 20 (.branch 19 (.leaf 3280238583) (.leaf 3193773556)) (.branch 21 (.leaf 3110347045) (.leaf 3029819029)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2952057335) (.leaf 2876937125)) (.branch 25 (.leaf 2804340426) (.leaf 2734155689))) (.branch 28 (.branch 27 (.leaf 2666277386) (.leaf 2600605635)) (.branch 29 (.leaf 2537045847) (.leaf 2475508406)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2415908362) (.branch 32 (.leaf 2358165157) (.leaf 2302202357))) (.branch 35 (.branch 34 (.leaf 2247947410) (.leaf 2195331421)) (.branch 36 (.leaf 2144288936) (.leaf 2094757743)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2046678690) (.leaf 1999995508)) (.branch 40 (.leaf 1954654647) (.leaf 1910605129))) (.branch 43 (.branch 42 (.leaf 1867798400) (.leaf 1826188198)) (.branch 44 (.leaf 1785730427) (.leaf 1746383040))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1708105926) (.branch 47 (.leaf 1670860809) (.leaf 1634611146))) (.branch 50 (.branch 49 (.leaf 1599322040) (.leaf 1564960148)) (.branch 51 (.leaf 1531493604) (.leaf 1498891940)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1467126012) (.leaf 1436167937)) (.branch 55 (.leaf 1405991025) (.leaf 1376569716))) (.branch 58 (.branch 57 (.leaf 1347879530) (.leaf 1319897008)) (.branch 59 (.leaf 1292599659) (.leaf 1265965920))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1239975102) (.branch 62 (.leaf 1214607353) (.leaf 1189843612))) (.branch 65 (.branch 64 (.leaf 1165665579) (.leaf 1142055668)) (.branch 66 (.leaf 1118996982) (.leaf 1096473275)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1074468925) (.leaf 1052968901)) (.branch 70 (.leaf 1031958739) (.leaf 1011424512))) (.branch 73 (.branch 72 (.leaf 991352812) (.leaf 971730717)) (.branch 74 (.leaf 952545778) (.leaf 933785992))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 915439783) (.branch 77 (.leaf 897495987) (.leaf 879943827))) (.branch 80 (.branch 79 (.leaf 862772904) (.leaf 845973172)) (.branch 81 (.leaf 829534931) (.leaf 813448807)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 797705739) (.leaf 782296966)) (.branch 85 (.leaf 767214017) (.leaf 752448695))) (.branch 88 (.branch 87 (.leaf 737993068) (.leaf 723839457)) (.branch 89 (.leaf 709980426) (.leaf 696408774)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 683117523) (.branch 92 (.leaf 670099910) (.leaf 657349378))) (.branch 95 (.branch 94 (.leaf 644859571) (.leaf 632624322)) (.branch 96 (.leaf 620637647) (.leaf 608893741)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 597386967) (.leaf 586111851)) (.branch 100 (.leaf 575063077) (.leaf 564235482))) (.branch 103 (.branch 102 (.leaf 553624047) (.leaf 543223895)) (.branch 104 (.leaf 533030283) (.leaf 523038601))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 513244363) (.leaf 503643205)) (.branch 108 (.leaf 494230883) (.leaf 485003263))) (.branch 111 (.branch 110 (.leaf 475956322) (.leaf 467086143)) (.branch 112 (.leaf 458388910) (.leaf 449860909)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 441498517) (.leaf 433298207)) (.branch 116 (.leaf 425256540) (.leaf 417370163))) (.branch 119 (.branch 118 (.leaf 409635808) (.leaf 402050287)) (.branch 120 (.leaf 394610491) (.leaf 387313387)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 631).q*(generalMeanRows 631).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 631).q*(generalMeanRows 631).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5177912125) (.branch 2 (.leaf 4999912467) (.leaf 4829862928))) (.branch 5 (.branch 4 (.leaf 4667312210) (.leaf 4511840802)) (.branch 6 (.leaf 4363058203) (.leaf 4220600453)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4084127915) (.leaf 3953323288)) (.branch 10 (.leaf 3827889823) (.leaf 3707549706))) (.branch 13 (.branch 12 (.leaf 3592042598) (.leaf 3481124316)) (.branch 14 (.leaf 3374565629) (.leaf 3272151163))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3173678406) (.branch 17 (.leaf 3078956794) (.leaf 2987806875))) (.branch 20 (.branch 19 (.leaf 2900059545) (.leaf 2815555347)) (.branch 21 (.leaf 2734143819) (.leaf 2655682904)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2580038396) (.leaf 2507083437)) (.branch 25 (.leaf 2436698044) (.leaf 2368768676))) (.branch 28 (.branch 27 (.leaf 2303187832) (.leaf 2239853679)) (.branch 29 (.leaf 2178669701) (.leaf 2119544382)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2062390901) (.branch 32 (.leaf 2007126858) (.leaf 1953674009))) (.branch 35 (.branch 34 (.leaf 1901958024) (.leaf 1851908265)) (.branch 36 (.leaf 1803457568) (.leaf 1756542049)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1711100917) (.leaf 1667076304)) (.branch 40 (.leaf 1624413096) (.leaf 1583058788))) (.branch 43 (.branch 42 (.leaf 1542963337) (.leaf 1504079032)) (.branch 44 (.leaf 1466360361) (.leaf 1429763903))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1394248208) (.branch 47 (.leaf 1359773698) (.leaf 1326302567))) (.branch 50 (.branch 49 (.leaf 1293798690) (.leaf 1262227532)) (.branch 51 (.leaf 1231556074) (.leaf 1201752726)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1172787262) (.leaf 1144630749)) (.branch 55 (.leaf 1117255480) (.leaf 1090634915))) (.branch 58 (.branch 57 (.leaf 1064743625) (.leaf 1039557233)) (.branch 59 (.leaf 1015052367) (.leaf 991206608))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 967998446) (.branch 62 (.leaf 945407237) (.leaf 923413160))) (.branch 65 (.branch 64 (.leaf 901997176) (.leaf 881141000)) (.branch 66 (.leaf 860827053) (.leaf 841038442)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 821758918) (.leaf 802972854)) (.branch 70 (.leaf 784665211) (.leaf 766821517))) (.branch 73 (.branch 72 (.leaf 749427835) (.leaf 732470746)) (.branch 74 (.leaf 715937320) (.leaf 699815100))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 684092075) (.branch 77 (.leaf 668756666) (.leaf 653797705))) (.branch 80 (.branch 79 (.leaf 639204419) (.leaf 624966409)) (.branch 81 (.leaf 611073638) (.leaf 597516417)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 584285386) (.leaf 571371502)) (.branch 85 (.leaf 558766029) (.leaf 546460520))) (.branch 88 (.branch 87 (.leaf 534446811) (.leaf 522717005)) (.branch 89 (.leaf 511263463) (.leaf 500078794)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 489155846) (.branch 92 (.leaf 478487694) (.leaf 468067633))) (.branch 95 (.branch 94 (.leaf 457889171) (.leaf 447946016)) (.branch 96 (.leaf 438232074) (.leaf 428741437)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 419468379) (.leaf 410407347)) (.branch 100 (.leaf 401552958) (.leaf 392899987))) (.branch 103 (.branch 102 (.leaf 384443367) (.leaf 376178180)) (.branch 104 (.leaf 368099652) (.leaf 360203150))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 352484174) (.leaf 344938354)) (.branch 108 (.leaf 337561445) (.leaf 330349322))) (.branch 111 (.branch 110 (.leaf 323297978) (.leaf 316403518)) (.branch 112 (.leaf 309662155) (.leaf 303070209)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 296624099) (.leaf 290320344)) (.branch 116 (.leaf 284155558) (.leaf 278126445))) (.branch 119 (.branch 118 (.leaf 272229800) (.leaf 266462503)) (.branch 120 (.leaf 260821517) (.leaf 255303886)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 632).q*(generalMeanRows 632).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 632).q*(generalMeanRows 632).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5301172010) (.branch 2 (.leaf 5121420713) (.leaf 4949666610))) (.branch 5 (.branch 4 (.leaf 4785455456) (.leaf 4628365028)) (.branch 6 (.leaf 4478002331) (.leaf 4334001106)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4196019597) (.leaf 4063738550)) (.branch 10 (.leaf 3936859409) (.leaf 3815102693))) (.branch 13 (.branch 12 (.leaf 3698206523) (.leaf 3585925291)) (.branch 14 (.leaf 3478028445) (.leaf 3374299394))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3274534495) (.branch 17 (.leaf 3178542134) (.leaf 3086141893))) (.branch 20 (.branch 19 (.leaf 2997163769) (.leaf 2911447469)) (.branch 21 (.leaf 2828841761) (.leaf 2749203869)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2672398924) (.leaf 2598299449)) (.branch 25 (.leaf 2526784888) (.leaf 2457741170))) (.branch 28 (.branch 27 (.leaf 2391060298) (.leaf 2326639981)) (.branch 29 (.leaf 2264383277) (.leaf 2204198274)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2145997782) (.branch 32 (.leaf 2089699057) (.leaf 2035223538))) (.branch 35 (.branch 34 (.leaf 1982496600) (.leaf 1931447325)) (.branch 36 (.leaf 1882008295) (.leaf 1834115384)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1787707580) (.leaf 1742726803)) (.branch 40 (.leaf 1699117747) (.leaf 1656827724))) (.branch 43 (.branch 42 (.leaf 1615806522) (.leaf 1576006268)) (.branch 44 (.leaf 1537381304) (.leaf 1499888066))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1463484973) (.branch 47 (.leaf 1428132324) (.leaf 1393792197))) (.branch 50 (.branch 49 (.leaf 1360428355) (.leaf 1328006162)) (.branch 51 (.leaf 1296492497) (.leaf 1265855679)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1236065394) (.leaf 1207092623)) (.branch 55 (.leaf 1178909579) (.leaf 1151489647))) (.branch 58 (.branch 57 (.leaf 1124807321) (.leaf 1098838155)) (.branch 59 (.leaf 1073558709) (.leaf 1048946497))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1024979948) (.branch 62 (.leaf 1001638354) (.leaf 978901834))) (.branch 65 (.branch 64 (.leaf 956751293) (.leaf 935168386)) (.branch 66 (.leaf 914135481) (.leaf 893635628)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 873652526) (.leaf 854170494)) (.branch 70 (.leaf 835174443) (.leaf 816649846))) (.branch 73 (.branch 72 (.leaf 798582719) (.leaf 780959590)) (.branch 74 (.leaf 763767480) (.leaf 746993881))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 730626733) (.branch 77 (.leaf 714654409) (.leaf 699065690))) (.branch 80 (.branch 79 (.leaf 683849755) (.leaf 668996155)) (.branch 81 (.leaf 654494806) (.leaf 640335967)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 626510231) (.leaf 613008507)) (.branch 85 (.leaf 599822007) (.leaf 586942237))) (.branch 88 (.branch 87 (.leaf 574360982) (.leaf 562070296)) (.branch 89 (.leaf 550062491) (.leaf 538330127)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526866000) (.branch 92 (.leaf 515663137) (.leaf 504714782))) (.branch 95 (.branch 94 (.leaf 494014393) (.leaf 483555627)) (.branch 96 (.leaf 473332339) (.leaf 463338572)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453568549) (.leaf 444016665)) (.branch 100 (.leaf 434677486) (.leaf 425545737))) (.branch 103 (.branch 102 (.leaf 416616299) (.leaf 407884202)) (.branch 104 (.leaf 399344623) (.leaf 390992875))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382824407) (.leaf 374834798)) (.branch 108 (.leaf 367019751) (.leaf 359375091))) (.branch 111 (.branch 110 (.leaf 351896757) (.leaf 344580804)) (.branch 112 (.leaf 337423393) (.leaf 330420791)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 323569368) (.leaf 316865590)) (.branch 116 (.leaf 310306019) (.leaf 303887308))) (.branch 119 (.branch 118 (.leaf 297606202) (.leaf 291459528)) (.branch 120 (.leaf 285444198) (.leaf 279557206)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 633).q*(generalMeanRows 633).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 633).q*(generalMeanRows 633).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5419838852) (.branch 2 (.leaf 5233811606) (.leaf 5056084845))) (.branch 5 (.branch 4 (.leaf 4886188149) (.leaf 4723684189)) (.branch 6 (.leaf 4568165837) (.leaf 4419253590)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4276593268) (.leaf 4139853946)) (.branch 10 (.leaf 4008726092) (.leaf 3882919887))) (.branch 13 (.branch 12 (.leaf 3762163714) (.leaf 3646202774)) (.branch 14 (.leaf 3534797841) (.leaf 3427724121))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3324770217) (.branch 17 (.leaf 3225737177) (.leaf 3130437628))) (.branch 20 (.branch 19 (.leaf 3038694980) (.leaf 2950342693)) (.branch 21 (.leaf 2865223606) (.leaf 2783189315)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2704099605) (.leaf 2627821918)) (.branch 25 (.leaf 2554230870) (.leaf 2483207794))) (.branch 28 (.branch 27 (.leaf 2414640323) (.leaf 2348422005)) (.branch 29 (.leaf 2284451934) (.leaf 2222634424)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2162878690) (.branch 32 (.leaf 2105098559) (.leaf 2049212202))) (.branch 35 (.branch 34 (.leaf 1995141874) (.leaf 1942813688)) (.branch 36 (.leaf 1892157384) (.leaf 1843106131)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1795596329) (.leaf 1749567432)) (.branch 40 (.leaf 1704961774) (.leaf 1661724416))) (.branch 43 (.branch 42 (.leaf 1619802993) (.leaf 1579147578)) (.branch 44 (.leaf 1539710546) (.leaf 1501446455))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1464311929) (.branch 47 (.leaf 1428265549) (.leaf 1393267749))) (.branch 50 (.branch 49 (.leaf 1359280725) (.leaf 1326268335)) (.branch 51 (.leaf 1294196023) (.leaf 1263030732)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1232740832) (.leaf 1203296043)) (.branch 55 (.leaf 1174667375) (.leaf 1146827057))) (.branch 58 (.branch 57 (.leaf 1119748481) (.leaf 1093406142)) (.branch 59 (.leaf 1067775587) (.leaf 1042833363))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1018556968) (.branch 62 (.leaf 994924805) (.leaf 971916143))) (.branch 65 (.branch 64 (.leaf 949511072) (.leaf 927690463)) (.branch 66 (.leaf 906435939) (.leaf 885729832)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 865555154) (.leaf 845895566)) (.branch 70 (.leaf 826735348) (.leaf 808059372))) (.branch 73 (.branch 72 (.leaf 789853072) (.leaf 772102422)) (.branch 74 (.leaf 754793914) (.leaf 737914528))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 721451719) (.branch 77 (.leaf 705393390) (.leaf 689727876))) (.branch 80 (.branch 79 (.leaf 674443923) (.leaf 659530674)) (.branch 81 (.leaf 644977650) (.leaf 630774731)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 616912148) (.leaf 603380462)) (.branch 85 (.leaf 590170554) (.leaf 577273610))) (.branch 88 (.branch 87 (.leaf 564681110) (.leaf 552384815)) (.branch 89 (.leaf 540376756) (.leaf 528649224)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 517194757) (.branch 92 (.leaf 506006136) (.leaf 495076367))) (.branch 95 (.branch 94 (.leaf 484398682) (.leaf 473966521)) (.branch 96 (.leaf 463773531) (.leaf 453813554)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 444080622) (.leaf 434568949)) (.branch 100 (.leaf 425272924) (.leaf 416187104))) (.branch 103 (.branch 102 (.leaf 407306209) (.leaf 398625117)) (.branch 104 (.leaf 390138855) (.leaf 381842595))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 373731653) (.leaf 365801476)) (.branch 108 (.leaf 358047643) (.leaf 350465862))) (.branch 111 (.branch 110 (.leaf 343051958) (.leaf 335801876)) (.branch 112 (.leaf 328711674) (.leaf 321777521)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 314995690) (.leaf 308362556)) (.branch 116 (.leaf 301874595) (.leaf 295528377))) (.branch 119 (.branch 118 (.leaf 289320566) (.leaf 283247914)) (.branch 120 (.leaf 277307261) (.leaf 271495531)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 634).q*(generalMeanRows 634).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 634).q*(generalMeanRows 634).cutoff/2-2 = (3242/1575:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable191.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5643207003) (.branch 2 (.leaf 5454852742) (.leaf 5274839873))) (.branch 5 (.branch 4 (.leaf 5102695004) (.leaf 4937978098)) (.branch 6 (.leaf 4780279569) (.leaf 4629217677)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4484436206) (.leaf 4345602380)) (.branch 10 (.leaf 4212404986) (.leaf 4084552679))) (.branch 13 (.branch 12 (.leaf 3961772451) (.leaf 3843808245)) (.branch 14 (.leaf 3730419693) (.leaf 3621380967))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3516479735) (.branch 17 (.leaf 3415516199) (.leaf 3318302224))) (.branch 20 (.branch 19 (.leaf 3224660533) (.leaf 3134423969)) (.branch 21 (.leaf 3047434818) (.leaf 2963544181)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2882611402) (.leaf 2804503529)) (.branch 25 (.leaf 2729094831) (.leaf 2656266334))) (.branch 28 (.branch 27 (.leaf 2585905402) (.leaf 2517905346)) (.branch 29 (.leaf 2452165058) (.leaf 2388588674)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2327085261) (.branch 32 (.leaf 2267568518) (.leaf 2209956509))) (.branch 35 (.branch 34 (.leaf 2154171407) (.leaf 2100139251)) (.branch 36 (.leaf 2047789731) (.leaf 1997055976)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1947874358) (.leaf 1900184315)) (.branch 40 (.leaf 1853928177) (.leaf 1809051007))) (.branch 43 (.branch 42 (.leaf 1765500452) (.leaf 1723226599)) (.branch 44 (.leaf 1682181849) (.leaf 1642320787))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1603600069) (.branch 47 (.leaf 1565978313) (.leaf 1529415991))) (.branch 50 (.branch 49 (.leaf 1493875339) (.leaf 1459320260)) (.branch 51 (.leaf 1425716239) (.leaf 1393030265)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1361230752) (.leaf 1330287467)) (.branch 55 (.leaf 1300171462) (.leaf 1270855011))) (.branch 58 (.branch 57 (.leaf 1242311547) (.leaf 1214515609)) (.branch 59 (.leaf 1187442783) (.leaf 1161069655))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1135373758) (.branch 62 (.leaf 1110333532) (.leaf 1085928277))) (.branch 65 (.branch 64 (.leaf 1062138112) (.leaf 1038943940)) (.branch 66 (.leaf 1016327405) (.leaf 994270864)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 972757349) (.leaf 951770538)) (.branch 70 (.leaf 931294728) (.leaf 911314800))) (.branch 73 (.branch 72 (.leaf 891816200) (.leaf 872784909)) (.branch 74 (.leaf 854207420) (.leaf 836070717))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 818362251) (.branch 77 (.leaf 801069923) (.leaf 784182059))) (.branch 80 (.branch 79 (.leaf 767687398) (.leaf 751575068)) (.branch 81 (.leaf 735834574) (.leaf 720455782)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705428900) (.leaf 690744468)) (.branch 85 (.leaf 676393340) (.leaf 662366676))) (.branch 88 (.branch 87 (.leaf 648655924) (.leaf 635252815)) (.branch 89 (.leaf 622149345) (.leaf 609337766)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 596810581) (.branch 92 (.leaf 584560526) (.leaf 572580566))) (.branch 95 (.branch 94 (.leaf 560863888) (.leaf 549403884)) (.branch 96 (.leaf 538194153) (.leaf 527228487)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516500865) (.leaf 506005447)) (.branch 100 (.leaf 495736565) (.leaf 485688721))) (.branch 103 (.branch 102 (.leaf 475856576) (.leaf 466234947)) (.branch 104 (.leaf 456818798) (.leaf 447603242))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 438583527) (.leaf 429755037)) (.branch 108 (.leaf 421113285) (.leaf 412653908))) (.branch 111 (.branch 110 (.leaf 404372666) (.leaf 396265432)) (.branch 112 (.leaf 388328195) (.leaf 380557051)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 372948201) (.leaf 365497947)) (.branch 116 (.leaf 358202691) (.leaf 351058928))) (.branch 119 (.branch 118 (.leaf 344063248) (.leaf 337212325)) (.branch 120 (.leaf 330502925) (.leaf 323931892)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 635).q*(generalMeanRows 635).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 635).q*(generalMeanRows 635).cutoff/2-2 = (3242/1575:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable191.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5519181576) (.branch 2 (.leaf 5337263511) (.leaf 5163379478))) (.branch 5 (.branch 4 (.leaf 4997072414) (.leaf 4837917538)) (.branch 6 (.leaf 4685519533) (.leaf 4539510031)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4399545362) (.leaf 4265304533)) (.branch 10 (.leaf 4136487413) (.leaf 4012813093))) (.branch 13 (.branch 12 (.leaf 3894018399) (.leaf 3779856553)) (.branch 14 (.leaf 3670095947) (.leaf 3564519034))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3462921308) (.branch 17 (.leaf 3365110387) (.leaf 3270905154))) (.branch 20 (.branch 19 (.leaf 3180134986) (.leaf 3092639034)) (.branch 21 (.leaf 3008265572) (.leaf 2926871385)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2848321217) (.leaf 2772487249)) (.branch 25 (.leaf 2699248627) (.leaf 2628491019))) (.branch 28 (.branch 27 (.leaf 2560106207) (.leaf 2493991707)) (.branch 29 (.leaf 2430050414) (.leaf 2368190281)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2308324008) (.branch 32 (.leaf 2250368763) (.leaf 2194245914))) (.branch 35 (.branch 34 (.leaf 2139880785) (.leaf 2087202426)) (.branch 36 (.leaf 2036143395) (.leaf 1986639563)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1938629919) (.leaf 1892056400)) (.branch 40 (.leaf 1846863723) (.leaf 1802999232))) (.branch 43 (.branch 42 (.leaf 1760412753) (.leaf 1719056458)) (.branch 44 (.leaf 1678884739) (.leaf 1639854086))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1601922976) (.branch 47 (.leaf 1565051769) (.leaf 1529202605))) (.branch 50 (.branch 49 (.leaf 1494339312) (.leaf 1460427320)) (.branch 51 (.leaf 1427433576) (.leaf 1395326464)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1364075737) (.leaf 1333652442)) (.branch 55 (.leaf 1304028859) (.leaf 1275178436))) (.branch 58 (.branch 57 (.leaf 1247075732) (.leaf 1219696361)) (.branch 59 (.leaf 1193016943) (.leaf 1167015051))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1141669167) (.branch 62 (.leaf 1116958638) (.leaf 1092863634))) (.branch 65 (.branch 64 (.leaf 1069365108) (.leaf 1046444761)) (.branch 66 (.leaf 1024085004) (.leaf 1002268926)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 980980265) (.leaf 960203373)) (.branch 70 (.leaf 939923192) (.leaf 920125226))) (.branch 73 (.branch 72 (.leaf 900795513) (.leaf 881920607)) (.branch 74 (.leaf 863487546) (.leaf 845483839))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 827897440) (.branch 77 (.leaf 810716732) (.leaf 793930506))) (.branch 80 (.branch 79 (.leaf 777527941) (.leaf 761498594)) (.branch 81 (.leaf 745832379) (.leaf 730519551)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 715550697) (.leaf 700916714)) (.branch 85 (.leaf 686608806) (.leaf 672618463))) (.branch 88 (.branch 87 (.leaf 658937452) (.leaf 645557810)) (.branch 89 (.leaf 632471824) (.leaf 619672031)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 607151201) (.branch 92 (.leaf 594902331) (.leaf 582918635))) (.branch 95 (.branch 94 (.leaf 571193536) (.leaf 559720657)) (.branch 96 (.leaf 548493816) (.leaf 537507016)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 526754438) (.leaf 516230435)) (.branch 100 (.leaf 505929527) (.leaf 495846393))) (.branch 103 (.branch 102 (.leaf 485975867) (.leaf 476312927)) (.branch 104 (.leaf 466852700) (.leaf 457590446))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 448521560) (.leaf 439641564)) (.branch 108 (.leaf 430946105) (.leaf 422430949))) (.branch 111 (.branch 110 (.leaf 414091977) (.leaf 405925182)) (.branch 112 (.leaf 397926664) (.leaf 390092628)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 382419378) (.leaf 374903318)) (.branch 116 (.leaf 367540943) (.leaf 360328840))) (.branch 119 (.branch 118 (.leaf 353263687) (.leaf 346342242)) (.branch 120 (.leaf 339561351) (.leaf 332917935)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 636).q*(generalMeanRows 636).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 636).q*(generalMeanRows 636).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5748148433) (.branch 2 (.leaf 5564192800) (.leaf 5388306224))) (.branch 5 (.branch 4 (.leaf 5220028689) (.leaf 5058932736)) (.branch 6 (.leaf 4904620611) (.leaf 4756721734)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4614890424) (.leaf 4478803866)) (.branch 10 (.leaf 4348160275) (.leaf 4222677240))) (.branch 13 (.branch 12 (.leaf 4102090231) (.leaf 3986151241)) (.branch 14 (.leaf 3874627552) (.leaf 3767300617))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3663965031) (.branch 17 (.leaf 3564427603) (.leaf 3468506491))) (.branch 20 (.branch 19 (.leaf 3376030425) (.leaf 3286837982)) (.branch 21 (.leaf 3200776923) (.leaf 3117703583)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3037482309) (.leaf 2959984936)) (.branch 25 (.leaf 2885090311) (.leaf 2812683843))) (.branch 28 (.branch 27 (.leaf 2742657094) (.leaf 2674907396)) (.branch 29 (.leaf 2609337493) (.leaf 2545855214)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2484373163) (.branch 32 (.leaf 2424808437) (.leaf 2367082353))) (.branch 35 (.branch 34 (.leaf 2311120207) (.leaf 2256851035)) (.branch 36 (.leaf 2204207402) (.leaf 2153125195)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2103543438) (.leaf 2055404109)) (.branch 40 (.leaf 2008651982) (.leaf 1963234462))) (.branch 43 (.branch 42 (.leaf 1919101448) (.leaf 1876205191)) (.branch 44 (.leaf 1834500165) (.leaf 1793942951))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1754492122) (.branch 47 (.leaf 1716108132) (.leaf 1678753224))) (.branch 50 (.branch 49 (.leaf 1642391328) (.leaf 1606987979)) (.branch 51 (.leaf 1572510229) (.leaf 1538926571)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1506206862) (.leaf 1474322258)) (.branch 55 (.leaf 1443245143) (.leaf 1412949072))) (.branch 58 (.branch 57 (.leaf 1383408707) (.leaf 1354599765)) (.branch 59 (.leaf 1326498967) (.leaf 1299083986))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1272333399) (.branch 62 (.leaf 1246226650) (.leaf 1220743998))) (.branch 65 (.branch 64 (.leaf 1195866488) (.leaf 1171575906)) (.branch 66 (.leaf 1147854748) (.leaf 1124686184)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1102054028) (.leaf 1079942709)) (.branch 70 (.leaf 1058337239) (.leaf 1037223191))) (.branch 73 (.branch 72 (.leaf 1016586668) (.leaf 996414285)) (.branch 74 (.leaf 976693140) (.leaf 957410796))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 938555260) (.branch 77 (.leaf 920114962) (.leaf 902078738))) (.branch 80 (.branch 79 (.leaf 884435812) (.leaf 867175778)) (.branch 81 (.leaf 850288584) (.leaf 833764520)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 817594200) (.leaf 801768549)) (.branch 85 (.leaf 786278792) (.leaf 771116439))) (.branch 88 (.branch 87 (.leaf 756273277) (.leaf 741741353)) (.branch 89 (.leaf 727512968) (.leaf 713580665)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 699937222) (.branch 92 (.leaf 686575636) (.leaf 673489123))) (.branch 95 (.branch 94 (.leaf 660671103) (.leaf 648115194)) (.branch 96 (.leaf 635815206) (.leaf 623765132)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 611959141) (.leaf 600391572)) (.branch 100 (.leaf 589056927) (.leaf 577949866))) (.branch 103 (.branch 102 (.leaf 567065200) (.leaf 556397888)) (.branch 104 (.leaf 545943028) (.leaf 535695853))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 525651730) (.leaf 515806151)) (.branch 108 (.leaf 506154728) (.leaf 496693193))) (.branch 111 (.branch 110 (.leaf 487417391) (.leaf 478323277)) (.branch 112 (.leaf 469406913) (.leaf 460664462)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 452092186) (.leaf 443686445)) (.branch 116 (.leaf 435443689) (.leaf 427360461))) (.branch 119 (.branch 118 (.leaf 419433388) (.leaf 411659182)) (.branch 120 (.leaf 404034638) (.leaf 396556627)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 637).q*(generalMeanRows 637).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 637).q*(generalMeanRows 637).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5973447966) (.branch 2 (.leaf 5780250440) (.leaf 5595577086))) (.branch 5 (.branch 4 (.leaf 5418941570) (.leaf 5249891942)) (.branch 6 (.leaf 5088007628) (.leaf 4932896758)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4784193763) (.leaf 4641557230)) (.branch 10 (.leaf 4504667962) (.leaf 4373227235))) (.branch 13 (.branch 12 (.leaf 4246955217) (.leaf 4125589537)) (.branch 14 (.leaf 4008883984) (.leaf 3896607322))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3788542211) (.branch 17 (.leaf 3684484219) (.leaf 3584240918))) (.branch 20 (.branch 19 (.leaf 3487631055) (.leaf 3394483794)) (.branch 21 (.leaf 3304638011) (.leaf 3217941651)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3134251136) (.leaf 3053430811)) (.branch 25 (.leaf 2975352439) (.leaf 2899894731))) (.branch 28 (.branch 27 (.leaf 2826942907) (.leaf 2756388296)) (.branch 29 (.leaf 2688127958) (.leaf 2622064334)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2558104925) (.branch 32 (.leaf 2496161987) (.leaf 2436152247))) (.branch 35 (.branch 34 (.leaf 2377996645) (.leaf 2321620088)) (.branch 36 (.leaf 2266951216) (.leaf 2213922194)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2162468506) (.leaf 2112528772)) (.branch 40 (.leaf 2064044571) (.leaf 2016960274))) (.branch 43 (.branch 42 (.leaf 1971222893) (.leaf 1926781935)) (.branch 44 (.leaf 1883589265) (.leaf 1841598981))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1800767290) (.branch 47 (.leaf 1761052399) (.leaf 1722414409))) (.branch 50 (.branch 49 (.leaf 1684815212) (.leaf 1648218400)) (.branch 51 (.leaf 1612589175) (.leaf 1577894266)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1544101853) (.leaf 1511181488)) (.branch 55 (.leaf 1479104031) (.leaf 1447841578))) (.branch 58 (.branch 57 (.leaf 1417367405) (.leaf 1387655905)) (.branch 59 (.leaf 1358682534) (.leaf 1330423760))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1302857009) (.branch 62 (.leaf 1275960625) (.leaf 1249713821))) (.branch 65 (.branch 64 (.leaf 1224096637) (.leaf 1199089903)) (.branch 66 (.leaf 1174675201) (.leaf 1150834827)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1127551762) (.leaf 1104809634)) (.branch 70 (.leaf 1082592695) (.leaf 1060885786))) (.branch 73 (.branch 72 (.leaf 1039674314) (.leaf 1018944225)) (.branch 74 (.leaf 998681979) (.leaf 978874529))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 959509295) (.branch 77 (.leaf 940574148) (.leaf 922057389))) (.branch 80 (.branch 79 (.leaf 903947726) (.leaf 886234262)) (.branch 81 (.leaf 868906475) (.leaf 851954202)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 835367624) (.leaf 819137253)) (.branch 85 (.leaf 803253914) (.leaf 787708738))) (.branch 88 (.branch 87 (.leaf 772493143) (.leaf 757598827)) (.branch 89 (.leaf 743017753) (.leaf 728742143)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 714764460) (.branch 92 (.leaf 701077407) (.leaf 687673912))) (.branch 95 (.branch 94 (.leaf 674547120) (.leaf 661690385)) (.branch 96 (.leaf 649097264) (.leaf 636761504)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 624677040) (.leaf 612837986)) (.branch 100 (.leaf 601238626) (.leaf 589873413))) (.branch 103 (.branch 102 (.leaf 578736956) (.leaf 567824019)) (.branch 104 (.leaf 557129515) (.leaf 546648499))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 536376163) (.leaf 526307834)) (.branch 108 (.leaf 516438963) (.leaf 506765128))) (.branch 111 (.branch 110 (.leaf 497282025) (.leaf 487985466)) (.branch 112 (.leaf 478871373) (.leaf 469935775)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 461174807) (.leaf 452584703)) (.branch 116 (.leaf 444161795) (.leaf 435902507))) (.branch 119 (.branch 118 (.leaf 427803356) (.leaf 419860945)) (.branch 120 (.leaf 412071963) (.leaf 404433183)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 638).q*(generalMeanRows 638).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 638).q*(generalMeanRows 638).cutoff/2-2 = (8210/3979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable211.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5139688504) (.branch 2 (.leaf 4970018736) (.leaf 4807952398))) (.branch 5 (.branch 4 (.leaf 4653048191) (.leaf 4504896392)) (.branch 6 (.leaf 4363116089) (.leaf 4227352724)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4097275883) (.leaf 3972577312)) (.branch 10 (.leaf 3852969135) (.leaf 3738182243))) (.branch 13 (.branch 12 (.leaf 3627964835) (.leaf 3522081094)) (.branch 14 (.leaf 3420309988) (.leaf 3322444174))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3228289000) (.branch 17 (.leaf 3137661594) (.leaf 3050390025))) (.branch 20 (.branch 19 (.leaf 2966312542) (.leaf 2885276868)) (.branch 21 (.leaf 2807139553) (.leaf 2731765381)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2659026819) (.leaf 2588803511)) (.branch 25 (.leaf 2520981810) (.leaf 2455454346))) (.branch 28 (.branch 27 (.leaf 2392119622) (.leaf 2330881645)) (.branch 29 (.leaf 2271649578) (.leaf 2214337425)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2158863727) (.branch 32 (.leaf 2105151287) (.leaf 2053126915))) (.branch 35 (.branch 34 (.leaf 2002721184) (.leaf 1953868206)) (.branch 36 (.leaf 1906505427) (.leaf 1860573426)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1816015737) (.leaf 1772778678)) (.branch 40 (.leaf 1730811189) (.leaf 1690064686))) (.branch 43 (.branch 42 (.leaf 1650492919) (.leaf 1612051841)) (.branch 44 (.leaf 1574699489) (.leaf 1538395862))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1503102822) (.branch 47 (.leaf 1468783984) (.leaf 1435404626))) (.branch 50 (.branch 49 (.leaf 1402931598) (.leaf 1371333240)) (.branch 51 (.leaf 1340579298) (.leaf 1310640855)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1281490258) (.leaf 1253101055)) (.branch 55 (.leaf 1225447928) (.leaf 1198506641))) (.branch 58 (.branch 57 (.leaf 1172253979) (.leaf 1146667700)) (.branch 59 (.leaf 1121726484) (.leaf 1097409888))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1073698304) (.branch 62 (.leaf 1050572912) (.leaf 1028015648))) (.branch 65 (.branch 64 (.leaf 1006009164) (.leaf 984536793)) (.branch 66 (.leaf 963582518) (.leaf 943130939)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 923167246) (.leaf 903677190)) (.branch 70 (.leaf 884647055) (.leaf 866063637))) (.branch 73 (.branch 72 (.leaf 847914218) (.leaf 830186544)) (.branch 74 (.leaf 812868805) (.leaf 795949614))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 779417987) (.branch 77 (.leaf 763263328) (.leaf 747475410))) (.branch 80 (.branch 79 (.leaf 732044359) (.leaf 716960638)) (.branch 81 (.leaf 702215035) (.leaf 687798647)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 673702866) (.leaf 659919369)) (.branch 85 (.leaf 646440106) (.leaf 633257285))) (.branch 88 (.branch 87 (.leaf 620363368) (.leaf 607751053)) (.branch 89 (.leaf 595413270) (.leaf 583343171)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 571534118) (.branch 92 (.leaf 559979678) (.leaf 548673613))) (.branch 95 (.branch 94 (.leaf 537609875) (.leaf 526782596)) (.branch 96 (.leaf 516186081) (.leaf 505814804)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 495663401) (.leaf 485726660)) (.branch 100 (.leaf 475999523) (.leaf 466477072))) (.branch 103 (.branch 102 (.leaf 457154530) (.leaf 448027255)) (.branch 104 (.leaf 439090731) (.leaf 430340569))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 421772500) (.leaf 413382370)) (.branch 108 (.leaf 405166138) (.leaf 397119871))) (.branch 111 (.branch 110 (.leaf 389239740) (.leaf 381522019)) (.branch 112 (.leaf 373963077) (.leaf 366559380)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 359307484) (.leaf 352204034)) (.branch 116 (.leaf 345245761) (.leaf 338429479))) (.branch 119 (.branch 118 (.leaf 331752080) (.leaf 325210539)) (.branch 120 (.leaf 318801900) (.leaf 312523286)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 639).q*(generalMeanRows 639).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 639).q*(generalMeanRows 639).cutoff/2-2 = (16330/7439:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable212.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5773860365) (.branch 2 (.leaf 5578867968) (.leaf 5392534404))) (.branch 5 (.branch 4 (.leaf 5214369302) (.leaf 5043916776)) (.branch 6 (.leaf 4880752415) (.leaf 4724480597)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4574732089) (.leaf 4431161891)) (.branch 10 (.leaf 4293447299) (.leaf 4161286154))) (.branch 13 (.branch 12 (.leaf 4034395260) (.leaf 3912508953)) (.branch 14 (.leaf 3795377798) (.leaf 3682767402))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3574457334) (.branch 17 (.leaf 3470240136) (.leaf 3369920419))) (.branch 20 (.branch 19 (.leaf 3273314035) (.leaf 3180247312)) (.branch 21 (.leaf 3090556357) (.leaf 3004086408)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2920691237) (.leaf 2840232607)) (.branch 25 (.leaf 2762579754) (.leaf 2687608924))) (.branch 28 (.branch 27 (.leaf 2615202932) (.leaf 2545250762)) (.branch 29 (.leaf 2477647183) (.leaf 2412292406)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2349091759) (.branch 32 (.leaf 2287955377) (.leaf 2228797927))) (.branch 35 (.branch 34 (.leaf 2171538341) (.leaf 2116099569)) (.branch 36 (.leaf 2062408353) (.leaf 2010395005)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1959993214) (.leaf 1911139852)) (.branch 40 (.leaf 1863774800) (.leaf 1817840780))) (.branch 43 (.branch 42 (.leaf 1773283202) (.leaf 1730050021)) (.branch 44 (.leaf 1688091592) (.leaf 1647360549))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1607811683) (.branch 47 (.leaf 1569401825) (.leaf 1532089741))) (.branch 50 (.branch 49 (.leaf 1495836033) (.leaf 1460603042)) (.branch 51 (.leaf 1426354758) (.leaf 1393056739)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1360676030) (.leaf 1329181085)) (.branch 55 (.leaf 1298541703) (.leaf 1268728956))) (.branch 58 (.branch 57 (.leaf 1239715126) (.leaf 1211473650)) (.branch 59 (.leaf 1183979058) (.leaf 1157206924))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1131133815) (.branch 62 (.leaf 1105737240) (.leaf 1080995611))) (.branch 65 (.branch 64 (.leaf 1056888196) (.leaf 1033395079)) (.branch 66 (.leaf 1010497123) (.leaf 988175934)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 966413825) (.leaf 945193786)) (.branch 70 (.leaf 924499451) (.leaf 904315068))) (.branch 73 (.branch 72 (.leaf 884625476) (.leaf 865416073)) (.branch 74 (.leaf 846672793) (.leaf 828382085))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 810530886) (.branch 77 (.leaf 793106604) (.leaf 776097092))) (.branch 80 (.branch 79 (.leaf 759490636) (.leaf 743275929)) (.branch 81 (.leaf 727442059) (.leaf 711978491)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 696875050) (.leaf 682121907)) (.branch 85 (.leaf 667709563) (.leaf 653628839))) (.branch 88 (.branch 87 (.leaf 639870858) (.leaf 626427038)) (.branch 89 (.leaf 613289075) (.leaf 600448936)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 587898845) (.branch 92 (.leaf 575631276) (.leaf 563638940))) (.branch 95 (.branch 94 (.leaf 551914778) (.leaf 540451951)) (.branch 96 (.leaf 529243832) (.leaf 518283999)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 507566223) (.leaf 497084467)) (.branch 100 (.leaf 486832873) (.leaf 476805759))) (.branch 103 (.branch 102 (.leaf 466997613) (.leaf 457403082)) (.branch 104 (.leaf 448016971) (.leaf 438834237))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 429849980) (.leaf 421059442)) (.branch 108 (.leaf 412457998) (.leaf 404041157))) (.branch 111 (.branch 110 (.leaf 395804550) (.leaf 387743933)) (.branch 112 (.leaf 379855177) (.leaf 372134268)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 364577301) (.leaf 357180476)) (.branch 116 (.leaf 349940097) (.leaf 342852567))) (.branch 119 (.branch 118 (.leaf 335914384) (.leaf 329122138)) (.branch 120 (.leaf 322472511) (.leaf 315962269)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 640).q*(generalMeanRows 640).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 640).q*(generalMeanRows 640).cutoff/2-2 = (4082/2001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable184.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5043408703) (.branch 2 (.leaf 4872069101) (.leaf 4708439442))) (.branch 5 (.branch 4 (.leaf 4552075055) (.leaf 4402562927)) (.branch 6 (.leaf 4259518938) (.leaf 4122585397)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3991428829) (.leaf 3865737990)) (.branch 10 (.leaf 3745222082) (.leaf 3629609140))) (.branch 13 (.branch 12 (.leaf 3518644572) (.leaf 3412089833)) (.branch 14 (.leaf 3309721228) (.leaf 3211328811))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3116715388) (.branch 17 (.leaf 3025695608) (.leaf 2938095118))) (.branch 20 (.branch 19 (.leaf 2853749807) (.leaf 2772505093)) (.branch 21 (.leaf 2694215284) (.leaf 2618742975)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2545958503) (.leaf 2475739438)) (.branch 25 (.leaf 2407970113) (.leaf 2342541194))) (.branch 28 (.branch 27 (.leaf 2279349274) (.leaf 2218296501)) (.branch 29 (.leaf 2159290236) (.leaf 2102242726)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2047070811) (.branch 32 (.leaf 1993695641) (.leaf 1942042420))) (.branch 35 (.branch 34 (.leaf 1892040166) (.leaf 1843621482)) (.branch 36 (.leaf 1796722350) (.leaf 1751281933)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1707242391) (.leaf 1664548710)) (.branch 40 (.leaf 1623148545) (.leaf 1582992065))) (.branch 43 (.branch 42 (.leaf 1544031813) (.leaf 1506222578)) (.branch 44 (.leaf 1469521267) (.leaf 1433886793))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1399279962) (.branch 47 (.leaf 1365663372) (.leaf 1333001320))) (.branch 50 (.branch 49 (.leaf 1301259709) (.leaf 1270405961)) (.branch 51 (.leaf 1240408941) (.leaf 1211238881)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1182867307) (.leaf 1155266975)) (.branch 55 (.leaf 1128411807) (.leaf 1102276830))) (.branch 58 (.branch 57 (.leaf 1076838123) (.leaf 1052072764)) (.branch 59 (.leaf 1027958779) (.leaf 1004475094))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 981601494) (.branch 62 (.leaf 959318580) (.leaf 937607726))) (.branch 65 (.branch 64 (.leaf 916451048) (.leaf 895831363)) (.branch 66 (.leaf 875732158) (.leaf 856137558)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 837032298) (.leaf 818401690)) (.branch 70 (.leaf 800231603) (.leaf 782508429))) (.branch 73 (.branch 72 (.leaf 765219067) (.leaf 748350896)) (.branch 74 (.leaf 731891755) (.leaf 715829919))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 700154086) (.branch 77 (.leaf 684853353) (.leaf 669917199))) (.branch 80 (.branch 79 (.leaf 655335472) (.leaf 641098370)) (.branch 81 (.leaf 627196427) (.leaf 613620498)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 600361748) (.leaf 587411634)) (.branch 85 (.leaf 574761900) (.leaf 562404559))) (.branch 88 (.branch 87 (.leaf 550331884) (.leaf 538536399)) (.branch 89 (.leaf 527010867) (.leaf 515748281)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 504741855) (.branch 92 (.leaf 493985017) (.leaf 483471397))) (.branch 95 (.branch 94 (.leaf 473194822) (.leaf 463149307)) (.branch 96 (.leaf 453329050) (.leaf 443728421)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 434341962) (.leaf 425164373)) (.branch 100 (.leaf 416190513) (.leaf 407415388))) (.branch 103 (.branch 102 (.leaf 398834151) (.leaf 390442094)) (.branch 104 (.leaf 382234644) (.leaf 374207356))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 366355913) (.leaf 358676117)) (.branch 108 (.leaf 351163887) (.leaf 343815255))) (.branch 111 (.branch 110 (.leaf 336626361) (.leaf 329593451)) (.branch 112 (.leaf 322712873) (.leaf 315981073)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 309394592) (.leaf 302950063)) (.branch 116 (.leaf 296644207) (.leaf 290473833))) (.branch 119 (.branch 118 (.leaf 284435833) (.leaf 278527177)) (.branch 120 (.leaf 272744918) (.leaf 267086180)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 641).q*(generalMeanRows 641).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 641).q*(generalMeanRows 641).cutoff/2-2 = (8122/3741:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable214.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5172946094) (.branch 2 (.leaf 5002178437) (.leaf 4839063410))) (.branch 5 (.branch 4 (.leaf 4683156858) (.leaf 4534046407)) (.branch 6 (.leaf 4391348681) (.leaf 4254706827)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4123788292) (.leaf 3998282828)) (.branch 10 (.leaf 3877900698) (.leaf 3762371050))) (.branch 13 (.branch 12 (.leaf 3651440453) (.leaf 3544871566)) (.branch 14 (.leaf 3442441926) (.leaf 3343942847))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3249178420) (.branch 17 (.leaf 3157964587) (.leaf 3070128307))) (.branch 20 (.branch 19 (.leaf 2985506781) (.leaf 2903946746)) (.branch 21 (.leaf 2825303825) (.leaf 2749441926)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2676232691) (.leaf 2605554987)) (.branch 25 (.leaf 2537294429) (.leaf 2471342954))) (.branch 28 (.branch 27 (.leaf 2407598407) (.leaf 2345964175)) (.branch 29 (.leaf 2286348833) (.leaf 2228665828)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2172833174) (.branch 32 (.leaf 2118773175) (.leaf 2066412167))) (.branch 35 (.branch 34 (.leaf 2015680273) (.leaf 1966511180)) (.branch 36 (.leaf 1918841928) (.leaf 1872612713)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1827766703) (.leaf 1784249868)) (.branch 40 (.leaf 1742010819) (.leaf 1701000656))) (.branch 43 (.branch 42 (.leaf 1661172830) (.leaf 1622483010)) (.branch 44 (.leaf 1584888960) (.leaf 1548350423))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1512829010) (.branch 47 (.leaf 1478288104) (.leaf 1444692757))) (.branch 50 (.branch 49 (.leaf 1412009605) (.leaf 1380206781)) (.branch 51 (.leaf 1349253838) (.leaf 1319121671)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1289782449) (.leaf 1261209546)) (.branch 55 (.leaf 1233377484) (.leaf 1206261867))) (.branch 58 (.branch 57 (.leaf 1179839330) (.leaf 1154087489)) (.branch 59 (.leaf 1128984885) (.leaf 1104510943))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1080645927) (.branch 62 (.leaf 1057370896) (.leaf 1034667670))) (.branch 65 (.branch 64 (.leaf 1012518788) (.leaf 990907475)) (.branch 66 (.leaf 969817610) (.leaf 949233695)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 929140822) (.leaf 909524650)) (.branch 70 (.leaf 890371376) (.leaf 871667710))) (.branch 73 (.branch 72 (.leaf 853400851) (.leaf 835558466)) (.branch 74 (.leaf 818128668) (.leaf 801099997))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 784461398) (.branch 77 (.leaf 768202207) (.leaf 752312129))) (.branch 80 (.branch 79 (.leaf 736781228) (.leaf 721599904)) (.branch 81 (.leaf 706758886) (.leaf 692249213)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 678062222) (.leaf 664189536)) (.branch 85 (.leaf 650623052) (.leaf 637354929))) (.branch 88 (.branch 87 (.leaf 624377578) (.leaf 611683652)) (.branch 89 (.leaf 599266035) (.leaf 587117833)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 575232367) (.branch 92 (.leaf 563603161) (.leaf 552223938))) (.branch 95 (.branch 94 (.leaf 541088609) (.leaf 530191269)) (.branch 96 (.leaf 519526187) (.leaf 509087800)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 498870710) (.leaf 488869671)) (.branch 100 (.leaf 479079592) (.leaf 469495524))) (.branch 103 (.branch 102 (.leaf 460112659) (.leaf 450926323)) (.branch 104 (.leaf 441931973) (.leaf 433125191))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 424501681) (.leaf 416057260)) (.branch 108 (.leaf 407787863) (.leaf 399689531))) (.branch 111 (.branch 110 (.leaf 391758410) (.leaf 383990749)) (.branch 112 (.leaf 376382895) (.leaf 368931290)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 361632469) (.leaf 354483055)) (.branch 116 (.leaf 347479757) (.leaf 340619368))) (.branch 119 (.branch 118 (.leaf 333898762) (.leaf 327314892)) (.branch 120 (.leaf 320864785) (.leaf 314545543)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 642).q*(generalMeanRows 642).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 642).q*(generalMeanRows 642).cutoff/2-2 = (16330/7439:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable212.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5206418885) (.branch 2 (.leaf 5034546235) (.leaf 4870375733))) (.branch 5 (.branch 4 (.leaf 4713460351) (.leaf 4563385044)) (.branch 6 (.leaf 4419763958) (.leaf 4282237930)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4150472255) (.leaf 4024154678)) (.branch 10 (.leaf 3902993587) (.leaf 3786716376))) (.branch 13 (.branch 12 (.leaf 3675067977) (.leaf 3567809510)) (.branch 14 (.leaf 3464717074) (.leaf 3365580634))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3270203010) (.branch 17 (.leaf 3178398956) (.leaf 3089994310))) (.branch 20 (.branch 19 (.leaf 3004825220) (.leaf 2922737431)) (.branch 21 (.leaf 2843585632) (.leaf 2767232851)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2693549898) (.leaf 2622414857)) (.branch 25 (.leaf 2553712603) (.leaf 2487334373))) (.branch 28 (.branch 27 (.leaf 2423177351) (.leaf 2361144300)) (.branch 29 (.leaf 2301143203) (.leaf 2243086946)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2186893013) (.branch 32 (.leaf 2132483206) (.leaf 2079783383))) (.branch 35 (.branch 34 (.leaf 2028723217) (.leaf 1979235964)) (.branch 36 (.leaf 1931258256) (.leaf 1884729904)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1839593707) (.leaf 1795795286)) (.branch 40 (.leaf 1753282919) (.leaf 1712007390))) (.branch 43 (.branch 42 (.leaf 1671921848) (.leaf 1632981677)) (.branch 44 (.leaf 1595144365) (.leaf 1558369396))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1522618134) (.branch 47 (.leaf 1487853722) (.leaf 1454040988))) (.branch 50 (.branch 49 (.leaf 1421146352) (.leaf 1389137741)) (.branch 51 (.leaf 1357984509) (.leaf 1327657365)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1298128296) (.leaf 1269370506)) (.branch 55 (.leaf 1241358349) (.leaf 1214067274))) (.branch 58 (.branch 57 (.leaf 1187473764) (.leaf 1161555289)) (.branch 59 (.leaf 1136290253) (.leaf 1111657946))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1087638506) (.branch 62 (.leaf 1064212869) (.leaf 1041362736))) (.branch 65 (.branch 64 (.leaf 1019070534) (.leaf 997319380)) (.branch 66 (.leaf 976093048) (.leaf 955375939)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 935153051) (.leaf 915409948)) (.branch 70 (.leaf 896132738) (.leaf 877308046))) (.branch 73 (.branch 72 (.leaf 858922986) (.leaf 840965148)) (.branch 74 (.leaf 823422567) (.leaf 806283707))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 789537444) (.branch 77 (.leaf 773173044) (.leaf 757180146))) (.branch 80 (.branch 79 (.leaf 741548748) (.leaf 726269190)) (.branch 81 (.leaf 711332139) (.leaf 696728578)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 682449787) (.leaf 668487334)) (.branch 85 (.leaf 654833065) (.leaf 641479087))) (.branch 88 (.branch 87 (.leaf 628417763) (.leaf 615641698)) (.branch 89 (.leaf 603143730) (.leaf 590916920)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 578954546) (.branch 92 (.leaf 567250090) (.leaf 555797235))) (.branch 95 (.branch 94 (.leaf 544589853) (.leaf 533621999)) (.branch 96 (.leaf 522887906) (.leaf 512381975)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 502098773) (.leaf 492033020)) (.branch 100 (.leaf 482179592) (.leaf 472533507))) (.branch 103 (.branch 102 (.leaf 463089928) (.leaf 453844150)) (.branch 104 (.leaf 444791600) (.leaf 435927832))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 427248521) (.leaf 418749459)) (.branch 108 (.leaf 410426553) (.leaf 402275818))) (.branch 111 (.branch 110 (.leaf 394293377) (.leaf 386475453)) (.branch 112 (.leaf 378818371) (.leaf 371318549)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 363972499) (.leaf 356776823)) (.branch 116 (.leaf 349728208) (.leaf 342823427))) (.branch 119 (.branch 118 (.leaf 336059334) (.leaf 329432861)) (.branch 120 (.leaf 322941017) (.leaf 316580885)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 643).q*(generalMeanRows 643).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 643).q*(generalMeanRows 643).cutoff/2-2 = (16330/7439:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable212.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4992486720) (.branch 2 (.leaf 4820501406) (.leaf 4656285744))) (.branch 5 (.branch 4 (.leaf 4499391914) (.leaf 4349403951)) (.branch 6 (.leaf 4205934958) (.leaf 4068624630)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3937137028) (.leaf 3811158584)) (.branch 10 (.leaf 3690396302) (.leaf 3574576138))) (.branch 13 (.branch 12 (.leaf 3463441533) (.leaf 3356752078)) (.branch 14 (.leaf 3254282308) (.leaf 3155820596))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3061168154) (.branch 17 (.leaf 2970138112) (.leaf 2882554673))) (.branch 20 (.branch 19 (.leaf 2798252352) (.leaf 2717075256)) (.branch 21 (.leaf 2638876443) (.leaf 2563517319)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2490867082) (.leaf 2420802217)) (.branch 25 (.leaf 2353206021) (.leaf 2287968168))) (.branch 28 (.branch 27 (.leaf 2224984305) (.leaf 2164155674)) (.branch 29 (.leaf 2105388768) (.leaf 2048595008)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1993690437) (.branch 32 (.leaf 1940595448) (.leaf 1889234517))) (.branch 35 (.branch 34 (.leaf 1839535964) (.leaf 1791431725)) (.branch 36 (.leaf 1744857143) (.leaf 1699750767)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1656054170) (.leaf 1613711776)) (.branch 40 (.leaf 1572670698) (.leaf 1532880589))) (.branch 43 (.branch 42 (.leaf 1494293496) (.leaf 1456863732)) (.branch 44 (.leaf 1420547749) (.leaf 1385304020))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1351092934) (.branch 47 (.leaf 1317876686) (.leaf 1285619189))) (.branch 50 (.branch 49 (.leaf 1254285974) (.leaf 1223844111)) (.branch 51 (.leaf 1194262126) (.leaf 1165509923)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1137558719) (.leaf 1110380969)) (.branch 55 (.leaf 1083950309) (.leaf 1058241494))) (.branch 58 (.branch 57 (.leaf 1033230339) (.leaf 1008893671)) (.branch 59 (.leaf 985209274) (.leaf 962155845))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 939712949) (.branch 62 (.leaf 917860976) (.leaf 896581098))) (.branch 65 (.branch 64 (.leaf 875855239) (.leaf 855666031)) (.branch 66 (.leaf 835996786) (.leaf 816831462)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 798154631) (.leaf 779951456)) (.branch 70 (.leaf 762207657) (.leaf 744909490))) (.branch 73 (.branch 72 (.leaf 728043719) (.leaf 711597600)) (.branch 74 (.leaf 695558849) (.leaf 679915630))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 664656532) (.branch 77 (.leaf 649770548) (.leaf 635247061))) (.branch 80 (.branch 79 (.leaf 621075827) (.leaf 607246956)) (.branch 81 (.leaf 593750899) (.leaf 580578434)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 567720651) (.leaf 555168939)) (.branch 85 (.leaf 542914976) (.leaf 530950713))) (.branch 88 (.branch 87 (.leaf 519268365) (.leaf 507860404)) (.branch 89 (.leaf 496719541) (.leaf 485838722)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 475211118) (.branch 92 (.leaf 464830115) (.leaf 454689306))) (.branch 95 (.branch 94 (.leaf 444782482) (.leaf 435103629)) (.branch 96 (.leaf 425646912) (.leaf 416406677)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 407377440) (.leaf 398553880)) (.branch 100 (.leaf 389930835) (.leaf 381503295))) (.branch 103 (.branch 102 (.leaf 373266398) (.leaf 365215423)) (.branch 104 (.leaf 357345783) (.leaf 349653027))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 342132829) (.leaf 334780984)) (.branch 108 (.leaf 327593408) (.leaf 320566130))) (.branch 111 (.branch 110 (.leaf 313695290) (.leaf 306977133)) (.branch 112 (.leaf 300408010) (.leaf 293984368)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 287702755) (.leaf 281559807)) (.branch 116 (.leaf 275552254) (.leaf 269676912))) (.branch 119 (.branch 118 (.leaf 263930681) (.leaf 258310543)) (.branch 120 (.leaf 252813560) (.leaf 247436870)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 644).q*(generalMeanRows 644).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 644).q*(generalMeanRows 644).cutoff/2-2 = (8122/3741:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable214.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5025310440) (.branch 2 (.leaf 4852194388) (.leaf 4686899069))) (.branch 5 (.branch 4 (.leaf 4528973722) (.leaf 4377999644)) (.branch 6 (.leaf 4233587396) (.leaf 4095374305)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3963022221) (.leaf 3836215516)) (.branch 10 (.leaf 3714659267) (.leaf 3598077630))) (.branch 13 (.branch 12 (.leaf 3486212357) (.leaf 3378821459)) (.branch 14 (.leaf 3275677988) (.leaf 3176568928))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3081294182) (.branch 17 (.leaf 2989665651) (.leaf 2901506385))) (.branch 20 (.branch 19 (.leaf 2816649807) (.leaf 2734939002)) (.branch 21 (.leaf 2656226062) (.leaf 2580371480)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2507243595) (.leaf 2436718079)) (.branch 25 (.leaf 2368677464) (.leaf 2303010697))) (.branch 28 (.branch 27 (.leaf 2239612738) (.leaf 2178384182)) (.branch 29 (.leaf 2119230907) (.leaf 2062063749)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2006798201) (.branch 32 (.leaf 1953354132) (.leaf 1901655522))) (.branch 35 (.branch 34 (.leaf 1851630220) (.leaf 1803209714)) (.branch 36 (.leaf 1756328922) (.leaf 1710925988)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1666942102) (.leaf 1624321323)) (.branch 40 (.leaf 1583010416) (.leaf 1542958702))) (.branch 43 (.branch 42 (.leaf 1504117913) (.leaf 1466442063)) (.branch 44 (.leaf 1429887315) (.leaf 1394411872))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1359975861) (.branch 47 (.leaf 1326541229) (.leaf 1294071651))) (.branch 50 (.branch 49 (.leaf 1262532432) (.leaf 1231890425)) (.branch 51 (.leaf 1202113949) (.leaf 1173172712)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1145037739) (.leaf 1117681306)) (.branch 55 (.leaf 1091076875) (.leaf 1065199033))) (.branch 58 (.branch 57 (.leaf 1040023440) (.leaf 1015526767)) (.branch 59 (.leaf 991686654) (.leaf 968481658))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 945891208) (.branch 62 (.leaf 923895566) (.leaf 902475781))) (.branch 65 (.branch 64 (.leaf 881613657) (.leaf 861291713)) (.branch 66 (.leaf 841493150) (.leaf 822201821)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 803402198) (.leaf 785079343)) (.branch 70 (.leaf 767218885) (.leaf 749806989))) (.branch 73 (.branch 72 (.leaf 732830333) (.leaf 716276086)) (.branch 74 (.leaf 700131887) (.leaf 684385820))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 669026398) (.branch 77 (.leaf 654042545) (.leaf 639423572))) (.branch 80 (.branch 79 (.leaf 625159167) (.leaf 611239376)) (.branch 81 (.leaf 597654588) (.leaf 584395519)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 571453200) (.leaf 558818966)) (.branch 85 (.leaf 546484437) (.leaf 534441514))) (.branch 88 (.branch 87 (.leaf 522682359) (.leaf 511199395)) (.branch 89 (.leaf 499985285) (.leaf 489032929)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478335452) (.branch 92 (.leaf 467886198) (.leaf 457678717))) (.branch 95 (.branch 94 (.leaf 447706760) (.leaf 437964271)) (.branch 96 (.leaf 428445380) (.leaf 419144394)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 410055793) (.leaf 401174221)) (.branch 100 (.leaf 392494483) (.leaf 384011536))) (.branch 103 (.branch 102 (.leaf 375720484) (.leaf 367616576)) (.branch 104 (.leaf 359695197) (.leaf 351951864))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 344382223) (.leaf 336982043)) (.branch 108 (.leaf 329747212) (.leaf 322673732))) (.branch 111 (.branch 110 (.leaf 315757718) (.leaf 308995392)) (.branch 112 (.leaf 302383079) (.leaf 295917205)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 289594292) (.leaf 283410957)) (.branch 116 (.leaf 277363906) (.leaf 271449936))) (.branch 119 (.branch 118 (.leaf 265665926) (.leaf 260008838)) (.branch 120 (.leaf 254475714) (.leaf 249063674)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 645).q*(generalMeanRows 645).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 645).q*(generalMeanRows 645).cutoff/2-2 = (8122/3741:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable214.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5877897164) (.branch 2 (.leaf 5687344784) (.leaf 5505172792))) (.branch 5 (.branch 4 (.leaf 5330904682) (.leaf 5164097589)) (.branch 6 (.leaf 5004339350) (.leaf 4851245883)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4704458841) (.leaf 4563643512)) (.branch 10 (.leaf 4428486920) (.leaf 4298696119))) (.branch 13 (.branch 12 (.leaf 4173996652) (.leaf 4054131143)) (.branch 14 (.leaf 3938858032) (.leaf 3827950411))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3721194973) (.branch 17 (.leaf 3618391043) (.leaf 3519349693))) (.branch 20 (.branch 19 (.leaf 3423892938) (.leaf 3331852983)) (.branch 21 (.leaf 3243071546) (.leaf 3157399223)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3074694908) (.leaf 2994825257)) (.branch 25 (.leaf 2917664189) (.leaf 2843092428))) (.branch 28 (.branch 27 (.leaf 2770997074) (.leaf 2701271213)) (.branch 29 (.leaf 2633813545) (.leaf 2568528046)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2505323649) (.branch 32 (.leaf 2444113946) (.leaf 2384816918))) (.branch 35 (.branch 34 (.leaf 2327354674) (.leaf 2271653211)) (.branch 36 (.leaf 2217642193) (.leaf 2165254736)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2114427218) (.leaf 2065099093)) (.branch 40 (.leaf 2017212718) (.leaf 1970713192))) (.branch 43 (.branch 42 (.leaf 1925548209) (.leaf 1881667910)) (.branch 44 (.leaf 1839024756) (.leaf 1797573399))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1757270565) (.branch 47 (.leaf 1718074948) (.leaf 1679947100))) (.branch 50 (.branch 49 (.leaf 1642849337) (.leaf 1606745645)) (.branch 51 (.leaf 1571601598) (.leaf 1537384269)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1504062161) (.leaf 1471605127)) (.branch 55 (.leaf 1439984307) (.leaf 1409172061))) (.branch 58 (.branch 57 (.leaf 1379141911) (.leaf 1349868478)) (.branch 59 (.leaf 1321327433) (.leaf 1293495442))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1266350121) (.branch 62 (.leaf 1239869986) (.leaf 1214034412))) (.branch 65 (.branch 64 (.leaf 1188823594) (.leaf 1164218503)) (.branch 66 (.leaf 1140200853) (.leaf 1116753066)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1093858236) (.leaf 1071500103)) (.branch 70 (.leaf 1049663017) (.leaf 1028331916))) (.branch 73 (.branch 72 (.leaf 1007492295) (.leaf 987130183)) (.branch 74 (.leaf 967232118) (.leaf 947785124))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 928776692) (.branch 77 (.leaf 910194757) (.leaf 892027677))) (.branch 80 (.branch 79 (.leaf 874264218) (.leaf 856893538)) (.branch 81 (.leaf 839905162) (.leaf 823288975)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 807035203) (.leaf 791134398)) (.branch 85 (.leaf 775577427) (.leaf 760355456))) (.branch 88 (.branch 87 (.leaf 745459940) (.leaf 730882610)) (.branch 89 (.leaf 716615461) (.leaf 702650744)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 688980953) (.branch 92 (.leaf 675598819) (.leaf 662497294))) (.branch 95 (.branch 94 (.leaf 649669551) (.leaf 637108967)) (.branch 96 (.leaf 624809123) (.leaf 612763788)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 600966921) (.leaf 589412655)) (.branch 100 (.leaf 578095296) (.leaf 567009316))) (.branch 103 (.branch 102 (.leaf 556149344) (.leaf 545510165)) (.branch 104 (.leaf 535086708) (.leaf 524874048))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 514867395) (.leaf 505062093)) (.branch 108 (.leaf 495453611) (.leaf 486037545))) (.branch 111 (.branch 110 (.leaf 476809607) (.leaf 467765626)) (.branch 112 (.leaf 458901541) (.leaf 450213398)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 441697349) (.leaf 433349644)) (.branch 116 (.leaf 425166630) (.leaf 417144749))) (.branch 119 (.branch 118 (.leaf 409280534) (.leaf 401570604)) (.branch 120 (.leaf 394011666) (.leaf 386600506)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 646).q*(generalMeanRows 646).c/2-2 = (1169/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable162.value]
    have hcontinuation : (generalMeanRows 646).q*(generalMeanRows 646).cutoff/2-2 = (3242/1575:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable191.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4872591141) (.branch 2 (.leaf 4700224184) (.leaf 4535681377))) (.branch 5 (.branch 4 (.leaf 4378514185) (.leaf 4228305828)) (.branch 6 (.leaf 4084668508) (.leaf 3947240939)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3815686133) (.leaf 3689689414)) (.branch 10 (.leaf 3568956629) (.leaf 3453212532))) (.branch 13 (.branch 12 (.leaf 3342199326) (.leaf 3235675337)) (.branch 14 (.leaf 3133413810) (.leaf 3035201812))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2940839234) (.branch 17 (.leaf 2850137880) (.leaf 2762920622))) (.branch 20 (.branch 19 (.leaf 2679020643) (.leaf 2598280724)) (.branch 21 (.leaf 2520552602) (.leaf 2445696371)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2373579932) (.leaf 2304078483)) (.branch 25 (.leaf 2237074054) (.leaf 2172455068))) (.branch 28 (.branch 27 (.leaf 2110115941) (.leaf 2049956704)) (.branch 29 (.leaf 1991882664) (.leaf 1935804075)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1881635841) (.branch 32 (.leaf 1829297237) (.leaf 1778711650))) (.branch 35 (.branch 34 (.leaf 1729806334) (.leaf 1682512187)) (.branch 36 (.leaf 1636763537) (.leaf 1592497949)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1549656037) (.leaf 1508181291)) (.branch 40 (.leaf 1468019919) (.leaf 1429120695))) (.branch 43 (.branch 42 (.leaf 1391434811) (.leaf 1354915756)) (.branch 44 (.leaf 1319519179) (.leaf 1285202779))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1251926195) (.branch 47 (.leaf 1219650898) (.leaf 1188340099))) (.branch 50 (.branch 49 (.leaf 1157958655) (.leaf 1128472983)) (.branch 51 (.leaf 1099850980) (.leaf 1072061946)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1045076513) (.leaf 1018866575)) (.branch 55 (.leaf 993405229) (.leaf 968666710))) (.branch 58 (.branch 57 (.leaf 944626336) (.leaf 921260455)) (.branch 59 (.leaf 898546392) (.leaf 876462407))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 854987640) (.branch 62 (.leaf 834102080) (.leaf 813786514))) (.branch 65 (.branch 64 (.leaf 794022497) (.leaf 774792310)) (.branch 66 (.leaf 756078928) (.leaf 737865991)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 720137765) (.leaf 702879123)) (.branch 70 (.leaf 686075509) (.leaf 669712918))) (.branch 73 (.branch 72 (.leaf 653777866) (.leaf 638257371)) (.branch 74 (.leaf 623138930) (.leaf 608410493))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 594060451) (.branch 77 (.leaf 580077610) (.leaf 566451177))) (.branch 80 (.branch 79 (.leaf 553170741) (.leaf 540226255)) (.branch 81 (.leaf 527608027) (.leaf 515306697)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 503313228) (.leaf 491618892)) (.branch 85 (.leaf 480215255) (.leaf 469094168))) (.branch 88 (.branch 87 (.leaf 458247755) (.leaf 447668397)) (.branch 89 (.leaf 437348730) (.leaf 427281628)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 417460198) (.branch 92 (.leaf 407877766) (.leaf 398527874))) (.branch 95 (.branch 94 (.leaf 389404269) (.leaf 380500894)) (.branch 96 (.leaf 371811882) (.leaf 363331549)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 355054386) (.leaf 346975055)) (.branch 100 (.leaf 339088378) (.leaf 331389336))) (.branch 103 (.branch 102 (.leaf 323873061) (.leaf 316534829)) (.branch 104 (.leaf 309370059) (.leaf 302374303))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 295543244) (.leaf 288872694)) (.branch 108 (.leaf 282358582) (.leaf 275996957))) (.branch 111 (.branch 110 (.leaf 269783983) (.leaf 263715929)) (.branch 112 (.leaf 257789174) (.leaf 252000197)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 246345576) (.leaf 240821985)) (.branch 116 (.leaf 235426190) (.leaf 230155046))) (.branch 119 (.branch 118 (.leaf 225005496) (.leaf 219974564)) (.branch 120 (.leaf 215059356) (.leaf 210257058)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 647).q*(generalMeanRows 647).c/2-2 = (6991/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable216.value]
    have hcontinuation : (generalMeanRows 647).q*(generalMeanRows 647).cutoff/2-2 = (16158/7525:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable217.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5683768799) (.branch 2 (.leaf 5491505706) (.leaf 5307755740))) (.branch 5 (.branch 4 (.leaf 5132038292) (.leaf 4963906504)) (.branch 6 (.leaf 4802944324) (.leaf 4648763876)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4501003114) (.leaf 4359323709)) (.branch 10 (.leaf 4223409154) (.leaf 4092963051))) (.branch 13 (.branch 12 (.leaf 3967707565) (.leaf 3847382021)) (.branch 14 (.leaf 3731741631) (.leaf 3620556330))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3513609723) (.branch 17 (.leaf 3410698117) (.leaf 3311629636))) (.branch 20 (.branch 19 (.leaf 3216223408) (.leaf 3124308824)) (.branch 21 (.leaf 3035724848) (.leaf 2950319388)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2867948715) (.leaf 2788476922)) (.branch 25 (.leaf 2711775430) (.leaf 2637722522))) (.branch 28 (.branch 27 (.leaf 2566202926) (.leaf 2497107406)) (.branch 29 (.leaf 2430332407) (.leaf 2365779704)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2303356087) (.branch 32 (.leaf 2242973063) (.leaf 2184546584))) (.branch 35 (.branch 34 (.leaf 2127996783) (.leaf 2073247737)) (.branch 36 (.leaf 2020227243) (.leaf 1968866603)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1919100430) (.leaf 1870866466)) (.branch 40 (.leaf 1824105405) (.leaf 1778760731))) (.branch 43 (.branch 42 (.leaf 1734778571) (.leaf 1692107548)) (.branch 44 (.leaf 1650698648) (.leaf 1610505094))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1571482228) (.branch 47 (.leaf 1533587401) (.leaf 1496779866))) (.branch 50 (.branch 49 (.leaf 1461020681) (.leaf 1426272614)) (.branch 51 (.leaf 1392500059) (.leaf 1359668951)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1327746688) (.leaf 1296702059)) (.branch 55 (.leaf 1266505174) (.leaf 1237127397))) (.branch 58 (.branch 57 (.leaf 1208541288) (.leaf 1180720541)) (.branch 59 (.leaf 1153639931) (.leaf 1127275260))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1101603311) (.branch 62 (.leaf 1076601796) (.leaf 1052249316))) (.branch 65 (.branch 64 (.leaf 1028525320) (.leaf 1005410060)) (.branch 66 (.leaf 982884558) (.leaf 960930571)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 939530553) (.leaf 918667627)) (.branch 70 (.leaf 898325553) (.leaf 878488699))) (.branch 73 (.branch 72 (.leaf 859142015) (.leaf 840271007)) (.branch 74 (.leaf 821861709) (.leaf 803900664))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 786374901) (.branch 77 (.leaf 769271911) (.leaf 752579632))) (.branch 80 (.branch 79 (.leaf 736286424) (.leaf 720381055)) (.branch 81 (.leaf 704852682) (.leaf 689690837)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 674885409) (.leaf 660426627)) (.branch 85 (.leaf 646305053) (.leaf 632511561))) (.branch 88 (.branch 87 (.leaf 619037329) (.leaf 605873824)) (.branch 89 (.leaf 593012792) (.leaf 580446246)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 568166456) (.branch 92 (.leaf 556165939) (.leaf 544437448))) (.branch 95 (.branch 94 (.leaf 532973964) (.leaf 521768689)) (.branch 96 (.leaf 510815033) (.leaf 500106609)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 489637227) (.leaf 479400881)) (.branch 100 (.leaf 469391751) (.leaf 459604185))) (.branch 103 (.branch 102 (.leaf 450032704) (.leaf 440671986)) (.branch 104 (.leaf 431516868) (.leaf 422562335))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 413803518) (.leaf 405235687)) (.branch 108 (.leaf 396854247) (.leaf 388654732))) (.branch 111 (.branch 110 (.leaf 380632803) (.leaf 372784242)) (.branch 112 (.leaf 365104946) (.leaf 357590927)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 350238307) (.leaf 343043311)) (.branch 116 (.leaf 336002269) (.leaf 329111607))) (.branch 119 (.branch 118 (.leaf 322367848) (.leaf 315767608)) (.branch 120 (.leaf 309307591) (.leaf 302984589)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 648).q*(generalMeanRows 648).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 648).q*(generalMeanRows 648).cutoff/2-2 = (403/198:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable186.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5093492471) (.branch 2 (.leaf 4924125418) (.leaf 4762312770))) (.branch 5 (.branch 4 (.leaf 4607619408) (.leaf 4459641210)) (.branch 6 (.leaf 4318002343) (.leaf 4182352846)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4052366463) (.leaf 3927738699)) (.branch 10 (.leaf 3808185076) (.leaf 3693439543))) (.branch 13 (.branch 12 (.leaf 3583253055) (.leaf 3477392273)) (.branch 14 (.leaf 3375638388) (.leaf 3277786046))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3183642371) (.branch 17 (.leaf 3093026073) (.leaf 3005766627))) (.branch 20 (.branch 19 (.leaf 2921703522) (.leaf 2840685574)) (.branch 21 (.leaf 2762570292) (.leaf 2687223294)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2614517768) (.leaf 2544333980)) (.branch 25 (.leaf 2476558807) (.leaf 2411085322))) (.branch 28 (.branch 27 (.leaf 2347812391) (.leaf 2286644315)) (.branch 29 (.leaf 2227490491) (.leaf 2170265094)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2114886789) (.branch 32 (.leaf 2061278454) (.leaf 2009366931))) (.branch 35 (.branch 34 (.leaf 1959082791) (.leaf 1910360109)) (.branch 36 (.leaf 1863136261) (.leaf 1817351732)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1772949940) (.leaf 1729877061)) (.branch 40 (.leaf 1688081879) (.leaf 1647515637))) (.branch 43 (.branch 42 (.leaf 1608131895) (.leaf 1569886411)) (.branch 44 (.leaf 1532737008) (.leaf 1496643472))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1461567435) (.branch 47 (.leaf 1427472284) (.leaf 1394323062))) (.branch 50 (.branch 49 (.leaf 1362086380) (.leaf 1330730336)) (.branch 51 (.leaf 1300224436) (.leaf 1270539519)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1241647690) (.leaf 1213522254)) (.branch 55 (.leaf 1186137654) (.leaf 1159469413))) (.branch 58 (.branch 57 (.leaf 1133494082) (.leaf 1108189184)) (.branch 59 (.leaf 1083533171) (.leaf 1059505372))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1036085956) (.branch 62 (.leaf 1013255884) (.leaf 990996879))) (.branch 65 (.branch 64 (.leaf 969291382) (.leaf 948122521)) (.branch 66 (.leaf 927474077) (.leaf 907330456)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 887676656) (.leaf 868498241)) (.branch 70 (.leaf 849781316) (.leaf 831512499))) (.branch 73 (.branch 72 (.leaf 813678903) (.leaf 796268108)) (.branch 74 (.leaf 779268141) (.leaf 762667460))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 746454931) (.branch 77 (.leaf 730619812) (.leaf 715151734))) (.branch 80 (.branch 79 (.leaf 700040687) (.leaf 685277002)) (.branch 81 (.leaf 670851341) (.leaf 656754678)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 642978287) (.leaf 629513733)) (.branch 85 (.leaf 616352854) (.leaf 603487756))) (.branch 88 (.branch 87 (.leaf 590910799) (.leaf 578614585)) (.branch 89 (.leaf 566591951) (.leaf 554835960)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543339890) (.branch 92 (.leaf 532097226) (.leaf 521101654))) (.branch 95 (.branch 94 (.leaf 510347050) (.leaf 499827476)) (.branch 96 (.leaf 489537171) (.leaf 479470543)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 469622167) (.leaf 459986776)) (.branch 100 (.leaf 450559254) (.leaf 441334633))) (.branch 103 (.branch 102 (.leaf 432308086) (.leaf 423474923)) (.branch 104 (.leaf 414830588) (.leaf 406370647))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 398090794) (.leaf 389986838)) (.branch 108 (.leaf 382054704) (.leaf 374290427))) (.branch 111 (.branch 110 (.leaf 366690149) (.leaf 359250115)) (.branch 112 (.leaf 351966669) (.leaf 344836254)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 337855403) (.leaf 331020742)) (.branch 116 (.leaf 324328982) (.leaf 317776923))) (.branch 119 (.branch 118 (.leaf 311361441) (.leaf 305079496)) (.branch 120 (.leaf 298928123) (.leaf 292904432)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 649).q*(generalMeanRows 649).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 649).q*(generalMeanRows 649).cutoff/2-2 = (1003/462:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable219.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4905146639) (.branch 2 (.leaf 4731628039) (.leaf 4565985862))) (.branch 5 (.branch 4 (.leaf 4407768581) (.leaf 4256556629)) (.branch 6 (.leaf 4111959618) (.leaf 3973613847)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3841180077) (.leaf 3714341529)) (.branch 10 (.leaf 3592802086) (.leaf 3476284662))) (.branch 13 (.branch 12 (.leaf 3364529738) (.leaf 3257294025)) (.branch 14 (.leaf 3154349252) (.leaf 3055481065))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2960488018) (.branch 17 (.leaf 2869180655) (.leaf 2781380669))) (.branch 20 (.branch 19 (.leaf 2696920124) (.leaf 2615640753)) (.branch 21 (.leaf 2537393303) (.leaf 2462036931)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2389438656) (.leaf 2319472844)) (.branch 25 (.leaf 2252020735) (.leaf 2186970006))) (.branch 28 (.branch 27 (.leaf 2124214369) (.leaf 2063653187)) (.branch 29 (.leaf 2005191134) (.leaf 1948737864)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1894207713) (.branch 32 (.leaf 1841519417) (.leaf 1790595850))) (.branch 35 (.branch 34 (.leaf 1741363780) (.leaf 1693753643)) (.branch 36 (.leaf 1647699331) (.leaf 1603137989)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1560009835) (.leaf 1518257982)) (.branch 40 (.leaf 1477828278) (.leaf 1438669154))) (.branch 43 (.branch 42 (.leaf 1400731478) (.leaf 1363968426)) (.branch 44 (.leaf 1328335351) (.leaf 1293789672))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1260290755) (.branch 47 (.leaf 1227799815) (.leaf 1196279818))) (.branch 50 (.branch 49 (.leaf 1165695385) (.leaf 1136012709)) (.branch 51 (.leaf 1107199472) (.leaf 1079224770)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1052059037) (.leaf 1025673982)) (.branch 55 (.leaf 1000042520) (.leaf 975138714))) (.branch 58 (.branch 57 (.leaf 950937718) (.leaf 927415721)) (.branch 59 (.leaf 904549898) (.leaf 882318361))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 860700114) (.branch 62 (.leaf 839675010) (.leaf 819223709))) (.branch 65 (.branch 64 (.leaf 799327641) (.leaf 779968970)) (.branch 66 (.leaf 761130558) (.leaf 742795933)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 724949259) (.leaf 707575306)) (.branch 70 (.leaf 690659421) (.leaf 674187506))) (.branch 73 (.branch 72 (.leaf 658145986) (.leaf 642521794)) (.branch 74 (.leaf 627302340) (.leaf 612475498))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 598029578) (.branch 77 (.leaf 583953313) (.leaf 570235837))) (.branch 80 (.branch 79 (.leaf 556866669) (.leaf 543835697)) (.branch 81 (.leaf 531133162) (.leaf 518749643)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 506676041) (.leaf 494903571)) (.branch 85 (.leaf 483423742) (.leaf 472228352))) (.branch 88 (.branch 87 (.leaf 461309469) (.leaf 450659427)) (.branch 89 (.leaf 440270811) (.leaf 430136447)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 420249396) (.branch 92 (.leaf 410602941) (.leaf 401190579))) (.branch 95 (.branch 94 (.leaf 392006016) (.leaf 383043154)) (.branch 96 (.leaf 374296088) (.leaf 365759095)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 357426630) (.leaf 349293318)) (.branch 100 (.leaf 341353947) (.leaf 333603465))) (.branch 103 (.branch 102 (.leaf 326036971) (.leaf 318649710)) (.branch 104 (.leaf 311437069) (.leaf 304394572))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 297517873) (.leaf 290802754)) (.branch 108 (.leaf 284245119) (.leaf 277840990))) (.branch 111 (.branch 110 (.leaf 271586505) (.leaf 265477908)) (.branch 112 (.leaf 259511555) (.leaf 253683899)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 247991498) (.leaf 242431002)) (.branch 116 (.leaf 236999155) (.leaf 231692793))) (.branch 119 (.branch 118 (.leaf 226508837) (.leaf 221444291)) (.branch 120 (.leaf 216496243) (.leaf 211661859)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 650).q*(generalMeanRows 650).c/2-2 = (6991/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable216.value]
    have hcontinuation : (generalMeanRows 650).q*(generalMeanRows 650).cutoff/2-2 = (16158/7525:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable217.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5259079054) (.branch 2 (.leaf 5089261775) (.leaf 4926989367))) (.branch 5 (.branch 4 (.leaf 4771824412) (.leaf 4623360806)) (.branch 6 (.leaf 4481221020) (.leaf 4345053658)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4214531267) (.leaf 4089348370)) (.branch 10 (.leaf 3969219692) (.leaf 3853878568))) (.branch 13 (.branch 12 (.leaf 3743075490) (.leaf 3636576801)) (.branch 14 (.leaf 3534163497) (.leaf 3435630145))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3340783894) (.branch 17 (.leaf 3249443565) (.leaf 3161438828))) (.branch 20 (.branch 19 (.leaf 3076609441) (.leaf 2994804548)) (.branch 21 (.leaf 2915882045) (.leaf 2839707985)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2766156036) (.leaf 2695106976)) (.branch 25 (.leaf 2626448230) (.leaf 2560073444))) (.branch 28 (.branch 27 (.leaf 2495882080) (.leaf 2433779055)) (.branch 29 (.leaf 2373674393) (.leaf 2315482911)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2259123921) (.branch 32 (.leaf 2204520960) (.leaf 2151601527))) (.branch 35 (.branch 34 (.leaf 2100296852) (.leaf 2050541670)) (.branch 36 (.leaf 2002274014) (.leaf 1955435023)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1909968760) (.leaf 1865822043)) (.branch 40 (.leaf 1822944288) (.leaf 1781287361))) (.branch 43 (.branch 42 (.leaf 1740805438) (.leaf 1701454878)) (.branch 44 (.leaf 1663194098) (.leaf 1625983463))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1589785175) (.branch 47 (.leaf 1554563175) (.leaf 1520283050))) (.branch 50 (.branch 49 (.leaf 1486911939) (.leaf 1454418458)) (.branch 51 (.leaf 1422772614) (.leaf 1391945736)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1361910402) (.leaf 1332640379)) (.branch 55 (.leaf 1304110557) (.leaf 1276296893))) (.branch 58 (.branch 57 (.leaf 1249176358) (.leaf 1222726882)) (.branch 59 (.leaf 1196927307) (.leaf 1171757344))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1147197526) (.branch 62 (.leaf 1123229171) (.leaf 1099834339))) (.branch 65 (.branch 64 (.leaf 1076995799) (.leaf 1054696996)) (.branch 66 (.leaf 1032922014) (.leaf 1011655549)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 990882879) (.leaf 970589837)) (.branch 70 (.leaf 950762784) (.leaf 931388585))) (.branch 73 (.branch 72 (.leaf 912454585) (.leaf 893948591)) (.branch 74 (.leaf 875858845) (.leaf 858174009))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 840883142) (.branch 77 (.leaf 823975688) (.leaf 807441455))) (.branch 80 (.branch 79 (.leaf 791270598) (.leaf 775453610)) (.branch 81 (.leaf 759981298) (.leaf 744844780)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 730035464) (.leaf 715545039)) (.branch 85 (.leaf 701365463) (.leaf 687488953))) (.branch 88 (.branch 87 (.leaf 673907971) (.leaf 660615217)) (.branch 89 (.leaf 647603619) (.leaf 634866323)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 622396685) (.branch 92 (.leaf 610188262) (.leaf 598234804))) (.branch 95 (.branch 94 (.leaf 586530250) (.leaf 575068715)) (.branch 96 (.leaf 563844487) (.leaf 552852020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 542085928) (.leaf 531540978)) (.branch 100 (.leaf 521212086) (.leaf 511094308))) (.branch 103 (.branch 102 (.leaf 501182840) (.leaf 491473009)) (.branch 104 (.leaf 481960272) (.leaf 472640207))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 463508513) (.leaf 454561002)) (.branch 108 (.leaf 445793597) (.leaf 437202332))) (.branch 111 (.branch 110 (.leaf 428783340) (.leaf 420532857)) (.branch 112 (.leaf 412447215) (.leaf 404522840)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 396756248) (.leaf 389144045)) (.branch 116 (.leaf 381682920) (.leaf 374369644))) (.branch 119 (.branch 118 (.leaf 367201070) (.leaf 360174126)) (.branch 120 (.leaf 353285817) (.leaf 346533219)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 651).q*(generalMeanRows 651).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5126874408) (.branch 2 (.leaf 4956397350) (.leaf 4793524208))) (.branch 5 (.branch 4 (.leaf 4637817010) (.leaf 4488868986)) (.branch 6 (.leaf 4346301841) (.leaf 4209763319)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4078925025) (.leaf 3953480472)) (.branch 10 (.leaf 3833143313) (.leaf 3717645756))) (.branch 13 (.branch 12 (.leaf 3606737123) (.leaf 3500182547)) (.branch 14 (.leaf 3397761783) (.leaf 3299268132))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3204507455) (.branch 17 (.leaf 3113297273) (.leaf 3025465942))) (.branch 20 (.branch 19 (.leaf 2940851900) (.leaf 2859302974)) (.branch 21 (.leaf 2780675736) (.leaf 2704834926)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2631652900) (.leaf 2561009139)) (.branch 25 (.leaf 2492789779) (.leaf 2426887190))) (.branch 28 (.branch 27 (.leaf 2363199578) (.leaf 2301630617)) (.branch 29 (.leaf 2242089108) (.leaf 2184488665)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2128747419) (.branch 32 (.leaf 2074787743) (.leaf 2022536002))) (.branch 35 (.branch 34 (.leaf 1971922307) (.leaf 1922880304)) (.branch 36 (.leaf 1875346958) (.leaf 1829262365)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1784569571) (.leaf 1741214399)) (.branch 40 (.leaf 1699145298) (.leaf 1658313191))) (.branch 43 (.branch 42 (.leaf 1618671335) (.leaf 1580175196)) (.branch 44 (.leaf 1542782322) (.leaf 1506452234))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1471146314) (.branch 47 (.leaf 1436827709) (.leaf 1403461232))) (.branch 50 (.branch 49 (.leaf 1371013276) (.leaf 1339451730)) (.branch 51 (.leaf 1308745899) (.leaf 1278866432)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1249785251) (.leaf 1221475485)) (.branch 55 (.leaf 1193911410) (.leaf 1167068390))) (.branch 58 (.branch 57 (.leaf 1140922821) (.leaf 1115452079)) (.branch 59 (.leaf 1090634474) (.leaf 1066449201))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1042876297) (.branch 62 (.leaf 1019896602) (.leaf 997491715))) (.branch 65 (.branch 64 (.leaf 975643963) (.leaf 954336364)) (.branch 66 (.leaf 933552594) (.leaf 913276955)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 893494347) (.leaf 874190240)) (.branch 70 (.leaf 855350647) (.leaf 836962100))) (.branch 73 (.branch 72 (.leaf 819011625) (.leaf 801486722)) (.branch 74 (.leaf 784375340) (.leaf 767665861))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 751347078) (.branch 77 (.leaf 735408178) (.leaf 719838724))) (.branch 80 (.branch 79 (.leaf 704628642) (.leaf 689768199)) (.branch 81 (.leaf 675247994) (.leaf 661058943)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 647192264) (.leaf 633639465)) (.branch 85 (.leaf 620392332) (.leaf 607442919))) (.branch 88 (.branch 87 (.leaf 594783534) (.leaf 582406732)) (.branch 89 (.leaf 570305304) (.leaf 558472266)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 546900853) (.branch 92 (.leaf 535584507) (.leaf 524516871))) (.branch 95 (.branch 94 (.leaf 513691783) (.leaf 503103266)) (.branch 96 (.leaf 492745519) (.leaf 482612916)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472699996) (.leaf 463001456)) (.branch 100 (.leaf 453512147) (.leaf 444227069))) (.branch 103 (.branch 102 (.leaf 435141364) (.leaf 426250310)) (.branch 104 (.leaf 417549321) (.leaf 409033936))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 400699818) (.leaf 392542750)) (.branch 108 (.leaf 384558630) (.leaf 376743467))) (.branch 111 (.branch 110 (.leaf 369093378) (.leaf 361604583)) (.branch 112 (.leaf 354273402) (.leaf 347096255)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 340069653) (.leaf 333190199)) (.branch 116 (.leaf 326454583) (.leaf 319859582))) (.branch 119 (.branch 118 (.leaf 313402054) (.leaf 307078938)) (.branch 120 (.leaf 300887250) (.leaf 294824081)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 652).q*(generalMeanRows 652).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 652).q*(generalMeanRows 652).cutoff/2-2 = (1003/462:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable219.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5160475124) (.branch 2 (.leaf 4988880787) (.leaf 4824940200))) (.branch 5 (.branch 4 (.leaf 4668212522) (.leaf 4518288317)) (.branch 6 (.leaf 4374786810) (.leaf 4237353436)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4105657649) (.leaf 3979390952)) (.branch 10 (.leaf 3858265122) (.leaf 3742010612))) (.branch 13 (.branch 12 (.leaf 3630375102) (.leaf 3523122184)) (.branch 14 (.leaf 3420030171) (.leaf 3320891009))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3225509285) (.branch 17 (.leaf 3133701326) (.leaf 3045294363))) (.branch 20 (.branch 19 (.leaf 2960125774) (.leaf 2878042389)) (.branch 21 (.leaf 2798899841) (.leaf 2722561982)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2648900333) (.leaf 2577793584)) (.branch 25 (.leaf 2509127125) (.leaf 2442792621))) (.branch 28 (.branch 27 (.leaf 2378687611) (.leaf 2316715137)) (.branch 29 (.leaf 2256783402) (.leaf 2198805455)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2142698890) (.branch 32 (.leaf 2088385571) (.leaf 2035791380))) (.branch 35 (.branch 34 (.leaf 1984845971) (.leaf 1935482555)) (.branch 36 (.leaf 1887637683) (.leaf 1841251059)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1796265355) (.leaf 1752626040)) (.branch 40 (.leaf 1710281225) (.leaf 1669181511))) (.branch 43 (.branch 42 (.leaf 1629279849) (.leaf 1590531412)) (.branch 44 (.leaf 1552893471) (.leaf 1516325281))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1480787973) (.branch 47 (.leaf 1446244449) (.leaf 1412659293))) (.branch 50 (.branch 49 (.leaf 1379998679) (.leaf 1348230283)) (.branch 51 (.leaf 1317323211) (.leaf 1287247918)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1257976144) (.leaf 1229480840)) (.branch 55 (.leaf 1201736115) (.leaf 1174717170))) (.branch 58 (.branch 57 (.leaf 1148400247) (.leaf 1122762574)) (.branch 59 (.leaf 1097782319) (.leaf 1073438539))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1049711142) (.branch 62 (.leaf 1026580841) (.leaf 1004029116))) (.branch 65 (.branch 64 (.leaf 982038178) (.leaf 960590933)) (.branch 66 (.leaf 939670949) (.leaf 919262426)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 899350166) (.leaf 879919543)) (.branch 70 (.leaf 860956478) (.leaf 842447416))) (.branch 73 (.branch 72 (.leaf 824379296) (.leaf 806739538)) (.branch 74 (.leaf 789516011) (.leaf 772697020))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 756271287) (.branch 77 (.leaf 740227925) (.leaf 724556432))) (.branch 80 (.branch 79 (.leaf 709246665) (.leaf 694288829)) (.branch 81 (.leaf 679673462) (.leaf 665391418)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 651433859) (.leaf 637792237)) (.branch 85 (.leaf 624458284) (.leaf 611424003))) (.branch 88 (.branch 87 (.leaf 598681650) (.leaf 586223733)) (.branch 89 (.leaf 574042994) (.leaf 562132405)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 550485154) (.branch 92 (.leaf 539094642) (.leaf 527954471))) (.branch 95 (.branch 94 (.leaf 517058437) (.leaf 506400524)) (.branch 96 (.leaf 495974894) (.leaf 485775884)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 475797996) (.leaf 466035893)) (.branch 100 (.leaf 456484393) (.leaf 447138463))) (.branch 103 (.branch 102 (.leaf 437993211) (.leaf 429043887)) (.branch 104 (.leaf 420285873) (.leaf 411714679))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403325940) (.leaf 395115412)) (.branch 108 (.leaf 387078966) (.leaf 379212583))) (.branch 111 (.branch 110 (.leaf 371512357) (.leaf 363974481)) (.branch 112 (.leaf 356595254) (.leaf 349371069)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342298415) (.leaf 335373874)) (.branch 116 (.leaf 328594114) (.leaf 321955890))) (.branch 119 (.branch 118 (.leaf 315456041) (.leaf 309091485)) (.branch 120 (.leaf 302859217) (.leaf 296756311)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 653).q*(generalMeanRows 653).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 653).q*(generalMeanRows 653).cutoff/2-2 = (1003/462:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable219.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4925566091) (.branch 2 (.leaf 4751239304) (.leaf 4584853110))) (.branch 5 (.branch 4 (.leaf 4425950274) (.leaf 4274106025)) (.branch 6 (.leaf 4128925216) (.leaf 3990039803)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3857106579) (.leaf 3729805139)) (.branch 10 (.leaf 3607836054) (.leaf 3490919217))) (.branch 13 (.branch 12 (.leaf 3378792346) (.leaf 3271209632)) (.branch 14 (.leaf 3167940504) (.leaf 3068768509))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2973490287) (.branch 17 (.leaf 2881914638) (.leaf 2793861663))) (.branch 20 (.branch 19 (.leaf 2709161981) (.leaf 2627656005)) (.branch 21 (.leaf 2549193284) (.leaf 2473631887)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2400837843) (.leaf 2330684620)) (.branch 25 (.leaf 2263052644) (.leaf 2197828857))) (.branch 28 (.branch 27 (.leaf 2134906302) (.leaf 2074183740)) (.branch 29 (.leaf 2015565302) (.leaf 1958960152)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1904282184) (.branch 32 (.leaf 1851449738) (.leaf 1800385332))) (.branch 35 (.branch 34 (.leaf 1751015418) (.leaf 1703270147)) (.branch 36 (.leaf 1657083156) (.leaf 1612391366)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1569134795) (.leaf 1527256380)) (.branch 40 (.leaf 1486701812) (.leaf 1447419387))) (.branch 43 (.branch 42 (.leaf 1409359853) (.leaf 1372476282)) (.branch 44 (.leaf 1336723938) (.leaf 1302060161))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1268444253) (.branch 47 (.leaf 1235837374) (.leaf 1204202440))) (.branch 50 (.branch 49 (.leaf 1173504037) (.leaf 1143708324)) (.branch 51 (.leaf 1114782961) (.leaf 1086697022)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1059420928) (.leaf 1032926379)) (.branch 55 (.leaf 1007186282) (.leaf 982174698))) (.branch 58 (.branch 57 (.leaf 957866782) (.leaf 934238724)) (.branch 59 (.leaf 911267705) (.leaf 888931843))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 867210149) (.branch 62 (.leaf 846082484) (.leaf 825529519))) (.branch 65 (.branch 64 (.leaf 805532695) (.leaf 786074185)) (.branch 66 (.leaf 767136863) (.leaf 748704269)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 730760576) (.leaf 713290567)) (.branch 70 (.leaf 696279600) (.leaf 679713585))) (.branch 73 (.branch 72 (.leaf 663578961) (.leaf 647862668)) (.branch 74 (.leaf 632552127) (.leaf 617635218))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 603100262) (.branch 77 (.leaf 588935998) (.leaf 575131566))) (.branch 80 (.branch 79 (.leaf 561676492) (.leaf 548560670)) (.branch 81 (.leaf 535774344) (.leaf 523308098)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 511152836) (.leaf 499299776)) (.branch 85 (.leaf 487740428) (.leaf 476466592))) (.branch 88 (.branch 87 (.leaf 465470336) (.leaf 454743994)) (.branch 89 (.leaf 444280149) (.leaf 434071628)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 424111487) (.branch 92 (.leaf 414393008) (.leaf 404909686))) (.branch 95 (.branch 94 (.leaf 395655221) (.leaf 386623511)) (.branch 96 (.leaf 377808647) (.leaf 369204901)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 360806721) (.leaf 352608726)) (.branch 100 (.leaf 344605699) (.leaf 336792578))) (.branch 103 (.branch 102 (.leaf 329164457) (.leaf 321716572)) (.branch 104 (.leaf 314444303) (.leaf 307343164))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 300408802) (.leaf 293636988)) (.branch 108 (.leaf 287023619) (.leaf 280564706))) (.branch 111 (.branch 110 (.leaf 274256376) (.leaf 268094867)) (.branch 112 (.leaf 262076521) (.leaf 256197783)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 250455199) (.leaf 244845409)) (.branch 116 (.leaf 239365148) (.leaf 234011239))) (.branch 119 (.branch 118 (.leaf 228780592) (.leaf 223670201)) (.branch 120 (.leaf 218677144) (.leaf 213798574)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 654).q*(generalMeanRows 654).c/2-2 = (6991/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable216.value]
    have hcontinuation : (generalMeanRows 654).q*(generalMeanRows 654).cutoff/2-2 = (8122/3741:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable214.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5040614457) (.branch 2 (.leaf 4864586473) (.leaf 4696543184))) (.branch 5 (.branch 4 (.leaf 4536024627) (.leaf 4382603520)) (.branch 6 (.leaf 4235882417) (.leaf 4095491154)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3961084576) (.leaf 3832340487)) (.branch 10 (.leaf 3708957804) (.leaf 3590654897))) (.branch 13 (.branch 12 (.leaf 3477168079) (.leaf 3368250246)) (.branch 14 (.leaf 3263669628) (.leaf 3163208669))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3066662986) (.branch 17 (.leaf 2973840434) (.leaf 2884560243))) (.branch 20 (.branch 19 (.leaf 2798652223) (.leaf 2715956041)) (.branch 21 (.leaf 2636320553) (.leaf 2559603188)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2485669382) (.leaf 2414392053)) (.branch 25 (.leaf 2345651117) (.leaf 2279333044))) (.branch 28 (.branch 27 (.leaf 2215330438) (.leaf 2153541654)) (.branch 29 (.leaf 2093870443) (.leaf 2036225620)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1980520753) (.branch 32 (.leaf 1926673877) (.leaf 1874607229))) (.branch 35 (.branch 34 (.leaf 1824246996) (.leaf 1775523084)) (.branch 36 (.leaf 1728368903) (.leaf 1682721159)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1638519669) (.leaf 1595707184)) (.branch 40 (.leaf 1554229222) (.leaf 1514033910))) (.branch 43 (.branch 42 (.leaf 1475071845) (.leaf 1437295952)) (.branch 44 (.leaf 1400661358) (.leaf 1365125275))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1330646880) (.branch 47 (.leaf 1297187217) (.leaf 1264709095))) (.branch 50 (.branch 49 (.leaf 1233176992) (.leaf 1202556968)) (.branch 51 (.leaf 1172816587) (.leaf 1143924831)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1115852035) (.leaf 1088569810)) (.branch 55 (.leaf 1062050986) (.leaf 1036269543))) (.branch 58 (.branch 57 (.leaf 1011200558) (.leaf 986820149)) (.branch 59 (.leaf 963105422) (.leaf 940034425))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 917586100) (.branch 62 (.leaf 895740241) (.leaf 874477451))) (.branch 65 (.branch 64 (.leaf 853779106) (.leaf 833627314)) (.branch 66 (.leaf 814004885) (.leaf 794895295)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 776282658) (.leaf 758151691)) (.branch 70 (.leaf 740487691) (.leaf 723276510))) (.branch 73 (.branch 72 (.leaf 706504523) (.leaf 690158609)) (.branch 74 (.leaf 674226131) (.leaf 658694908))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 643553199) (.branch 77 (.leaf 628789684) (.leaf 614393444))) (.branch 80 (.branch 79 (.leaf 600353944) (.leaf 586661017)) (.branch 81 (.leaf 573304849) (.leaf 560275962)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 547565201) (.leaf 535163723)) (.branch 85 (.leaf 523062979) (.leaf 511254707))) (.branch 88 (.branch 87 (.leaf 499730916) (.leaf 488483878)) (.branch 89 (.leaf 477506118) (.leaf 466790400)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 456329721) (.branch 92 (.leaf 446117302) (.leaf 436146575))) (.branch 95 (.branch 94 (.leaf 426411182) (.leaf 416904960)) (.branch 96 (.leaf 407621938) (.leaf 398556328)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 389702516) (.leaf 381055062)) (.branch 100 (.leaf 372608687) (.leaf 364358270))) (.branch 103 (.branch 102 (.leaf 356298841) (.leaf 348425579)) (.branch 104 (.leaf 340733800) (.leaf 333218960))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 325876645) (.leaf 318702567)) (.branch 108 (.leaf 311692560) (.leaf 304842577))) (.branch 111 (.branch 110 (.leaf 298148686) (.leaf 291607063)) (.branch 112 (.leaf 285213992) (.leaf 278965859)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 272859150) (.leaf 266890447)) (.branch 116 (.leaf 261056425) (.leaf 255353850))) (.branch 119 (.branch 118 (.leaf 249779573) (.leaf 244330531)) (.branch 120 (.leaf 239003744) (.leaf 233796306)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 655).q*(generalMeanRows 655).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 655).q*(generalMeanRows 655).cutoff/2-2 = (8122/3741:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable214.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4974240484) (.branch 2 (.leaf 4801802004) (.leaf 4637146478))) (.branch 5 (.branch 4 (.leaf 4479826548) (.leaf 4329426632)) (.branch 6 (.leaf 4185560145) (.leaf 4047867031)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3916011539) (.leaf 3789680237)) (.branch 10 (.leaf 3668580216) (.leaf 3552437476))) (.branch 13 (.branch 12 (.leaf 3440995460) (.leaf 3334013725)) (.branch 14 (.leaf 3231266739) (.leaf 3132542780))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3037642937) (.branch 17 (.leaf 2946380191) (.leaf 2858578579))) (.branch 20 (.branch 19 (.leaf 2774072424) (.leaf 2692705630)) (.branch 21 (.leaf 2614331034) (.leaf 2538809806)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2466010899) (.leaf 2395810542)) (.branch 25 (.leaf 2328091766) (.leaf 2262743972))) (.branch 28 (.branch 27 (.leaf 2199662528) (.leaf 2138748391)) (.branch 29 (.leaf 2079907768) (.leaf 2023051783)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1968096189) (.branch 32 (.leaf 1914961081) (.leaf 1863570638))) (.branch 35 (.branch 34 (.leaf 1813852883) (.leaf 1765739455)) (.branch 36 (.leaf 1719165402) (.leaf 1674068977)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1630391461) (.leaf 1588076987)) (.branch 40 (.leaf 1547072381) (.leaf 1507327011))) (.branch 43 (.branch 42 (.leaf 1468792642) (.leaf 1431423309)) (.branch 44 (.leaf 1395175190) (.leaf 1360006489))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1325877327) (.branch 47 (.leaf 1292749639) (.leaf 1260587080))) (.branch 50 (.branch 49 (.leaf 1229354929) (.leaf 1199020008)) (.branch 51 (.leaf 1169550599) (.leaf 1140916371)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1113088305) (.leaf 1086038631)) (.branch 55 (.leaf 1059740759) (.leaf 1034169227))) (.branch 58 (.branch 57 (.leaf 1009299637) (.leaf 985108609)) (.branch 59 (.leaf 961573723) (.leaf 938673479))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 916387249) (.branch 62 (.leaf 894695234) (.leaf 873578426))) (.branch 65 (.branch 64 (.leaf 853018568) (.leaf 832998120)) (.branch 66 (.leaf 813500225) (.leaf 794508678)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 776007893) (.leaf 757982876)) (.branch 70 (.leaf 740419199) (.leaf 723302972))) (.branch 73 (.branch 72 (.leaf 706620819) (.leaf 690359857)) (.branch 74 (.leaf 674507671) (.leaf 659052298))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 643982200) (.branch 77 (.leaf 629286252) (.leaf 614953720))) (.branch 80 (.branch 79 (.leaf 600974248) (.leaf 587337837)) (.branch 81 (.leaf 574034833) (.leaf 561055913)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 548392070) (.leaf 536034598)) (.branch 85 (.leaf 523975083) (.leaf 512205390))) (.branch 88 (.branch 87 (.leaf 500717651) (.leaf 489504253)) (.branch 89 (.leaf 478557832) (.leaf 467871258)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 457437629) (.branch 92 (.leaf 447250263) (.leaf 437302685))) (.branch 95 (.branch 94 (.leaf 427588624) (.leaf 418102003)) (.branch 96 (.leaf 408836929) (.leaf 399787693)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 390948755) (.leaf 382314744)) (.branch 100 (.leaf 373880449) (.leaf 365640814))) (.branch 103 (.branch 102 (.leaf 357590930) (.leaf 349726034)) (.branch 104 (.leaf 342041500) (.leaf 334532838))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 327195683) (.leaf 320025799)) (.branch 108 (.leaf 313019066) (.leaf 306171484))) (.branch 111 (.branch 110 (.leaf 299479161) (.leaf 292938317)) (.branch 112 (.leaf 286545275) (.leaf 280296458)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 274188390) (.leaf 268217686)) (.branch 116 (.leaf 262381056) (.leaf 256675296))) (.branch 119 (.branch 118 (.leaf 251097290) (.leaf 245644002)) (.branch 120 (.leaf 240312479) (.leaf 235099846)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 656).q*(generalMeanRows 656).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 656).q*(generalMeanRows 656).cutoff/2-2 = (1003/462:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable219.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5039654898) (.branch 2 (.leaf 4864948743) (.leaf 4698127892))) (.branch 5 (.branch 4 (.leaf 4538739105) (.leaf 4386361335)) (.branch 6 (.leaf 4240602913) (.leaf 4101099047)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3967509572) (.leaf 3839516933)) (.branch 10 (.leaf 3716824370) (.leaf 3599154280))) (.branch 13 (.branch 12 (.leaf 3486246730) (.leaf 3377858118)) (.branch 14 (.leaf 3273759944) (.leaf 3173737702))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3077589866) (.branch 17 (.leaf 2985126958) (.leaf 2896170699))) (.branch 20 (.branch 19 (.leaf 2810553234) (.leaf 2728116415)) (.branch 21 (.leaf 2648711143) (.leaf 2572196763)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2498440505) (.leaf 2427316968)) (.branch 25 (.leaf 2358707648) (.leaf 2292500489))) (.branch 28 (.branch 27 (.leaf 2228589484) (.leaf 2166874288)) (.branch 29 (.leaf 2107259872) (.leaf 2049656196)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1993977901) (.branch 32 (.leaf 1940144032) (.leaf 1888077772))) (.branch 35 (.branch 34 (.leaf 1837706197) (.leaf 1788960048)) (.branch 36 (.leaf 1741773516) (.leaf 1696084044)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1651832141) (.leaf 1608961205)) (.branch 40 (.leaf 1567417363) (.leaf 1527149316))) (.branch 43 (.branch 42 (.leaf 1488108196) (.leaf 1450247433)) (.branch 44 (.leaf 1413522628) (.leaf 1377891436))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1343313453) (.branch 47 (.leaf 1309750116) (.leaf 1277164598))) (.branch 50 (.branch 49 (.leaf 1245521725) (.leaf 1214787880)) (.branch 51 (.leaf 1184930930) (.leaf 1155920144)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1127726122) (.leaf 1100320727)) (.branch 55 (.leaf 1073677022) (.leaf 1047769207))) (.branch 58 (.branch 57 (.leaf 1022572567) (.leaf 998063411)) (.branch 59 (.leaf 974219026) (.leaf 951017630))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 928438322) (.branch 62 (.leaf 906461044) (.leaf 885066536))) (.branch 65 (.branch 64 (.leaf 864236302) (.leaf 843952573)) (.branch 66 (.leaf 824198268) (.leaf 804956971)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 786212889) (.leaf 767950831)) (.branch 70 (.leaf 750156181) (.leaf 732814864))) (.branch 73 (.branch 72 (.leaf 715913330) (.leaf 699438526)) (.branch 74 (.leaf 683377875) (.leaf 667719253))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 652450974) (.branch 77 (.leaf 637561765) (.leaf 623040751))) (.branch 80 (.branch 79 (.leaf 608877440) (.leaf 595061701)) (.branch 81 (.leaf 581583755) (.leaf 568434154)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 555603773) (.leaf 543083792)) (.branch 85 (.leaf 530865687) (.leaf 518941215))) (.branch 88 (.branch 87 (.leaf 507302405) (.leaf 495941544)) (.branch 89 (.leaf 484851170) (.leaf 474024061)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 463453224) (.branch 92 (.leaf 453131887) (.leaf 443053493))) (.branch 95 (.branch 94 (.leaf 433211686) (.leaf 423600309)) (.branch 96 (.leaf 414213394) (.leaf 405045154)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 396089979) (.leaf 387342425)) (.branch 100 (.leaf 378797214) (.leaf 370449222))) (.branch 103 (.branch 102 (.leaf 362293477) (.leaf 354325153)) (.branch 104 (.leaf 346539563) (.leaf 338932156))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 331498514) (.leaf 324234341)) (.branch 108 (.leaf 317135465) (.leaf 310197833))) (.branch 111 (.branch 110 (.leaf 303417502) (.leaf 296790641)) (.branch 112 (.leaf 290313527) (.leaf 283982534)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 277794141) (.leaf 271744919)) (.branch 116 (.leaf 265831533) (.leaf 260050739))) (.branch 119 (.branch 118 (.leaf 254399378) (.leaf 248874376)) (.branch 120 (.leaf 243472741) (.leaf 238191558)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 657).q*(generalMeanRows 657).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 657).q*(generalMeanRows 657).cutoff/2-2 = (1003/462:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable219.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7797508124) (.branch 2 (.leaf 7567580301) (.leaf 7346759867))) (.branch 5 (.branch 4 (.leaf 7134572603) (.leaf 6930576900)) (.branch 6 (.leaf 6734360810) (.leaf 6545539427)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6363752564) (.leaf 6188662686)) (.branch 10 (.leaf 6019953058) (.leaf 5857326089))) (.branch 13 (.branch 12 (.leaf 5700501839) (.leaf 5549216680)) (.branch 14 (.leaf 5403222075) (.leaf 5262283485))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5126179365) (.branch 17 (.leaf 4994700257) (.leaf 4867647961))) (.branch 20 (.branch 19 (.leaf 4744834778) (.leaf 4626082813)) (.branch 21 (.leaf 4511223340) (.leaf 4400096220)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4292549358) (.leaf 4188438207)) (.branch 25 (.leaf 4087625312) (.leaf 3989979885))) (.branch 28 (.branch 27 (.leaf 3895377408) (.leaf 3803699275)) (.branch 29 (.leaf 3714832447) (.leaf 3628669141)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3545106537) (.branch 32 (.leaf 3464046503) (.leaf 3385395339))) (.branch 35 (.branch 34 (.leaf 3309063543) (.leaf 3234965582)) (.branch 36 (.leaf 3163019689) (.leaf 3093147666)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3025274697) (.leaf 2959329180)) (.branch 40 (.leaf 2895242564) (.leaf 2832949199))) (.branch 43 (.branch 42 (.leaf 2772386186) (.leaf 2713493252)) (.branch 44 (.leaf 2656212614) (.leaf 2600488866))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2546268862) (.branch 47 (.leaf 2493501608) (.leaf 2442138168))) (.branch 50 (.branch 49 (.leaf 2392131560) (.leaf 2343436672)) (.branch 51 (.leaf 2296010172) (.leaf 2249810432)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2204797446) (.leaf 2160932761)) (.branch 55 (.leaf 2118179407) (.leaf 2076501831))) (.branch 58 (.branch 57 (.leaf 2035865834) (.leaf 1996238515)) (.branch 59 (.leaf 1957588212) (.leaf 1919884448))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1883097883) (.branch 62 (.leaf 1847200265) (.leaf 1812164383))) (.branch 65 (.branch 64 (.leaf 1777964024) (.leaf 1744573928)) (.branch 66 (.leaf 1711969755) (.leaf 1680128040)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1649026164) (.leaf 1618642311)) (.branch 70 (.leaf 1588955444) (.leaf 1559945265))) (.branch 73 (.branch 72 (.leaf 1531592194) (.leaf 1503877332)) (.branch 74 (.leaf 1476782440) (.leaf 1450289908))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1424382734) (.branch 77 (.leaf 1399044498) (.leaf 1374259340))) (.branch 80 (.branch 79 (.leaf 1350011937) (.leaf 1326287484)) (.branch 81 (.leaf 1303071673) (.leaf 1280350671)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1258111109) (.leaf 1236340058)) (.branch 85 (.leaf 1215025012) (.leaf 1194153877))) (.branch 88 (.branch 87 (.leaf 1173714953) (.leaf 1153696916)) (.branch 89 (.leaf 1134088811) (.leaf 1114880030)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1096060305) (.branch 92 (.leaf 1077619695) (.leaf 1059548572))) (.branch 95 (.branch 94 (.leaf 1041837609) (.leaf 1024477771)) (.branch 96 (.leaf 1007460306) (.leaf 990776728)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 974418817) (.leaf 958378600)) (.branch 100 (.leaf 942648350) (.leaf 927220571))) (.branch 103 (.branch 102 (.leaf 912087995) (.leaf 897243571)) (.branch 104 (.leaf 882680456) (.leaf 868392013))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 854371799) (.leaf 840613558)) (.branch 108 (.leaf 827111220) (.leaf 813858888))) (.branch 111 (.branch 110 (.leaf 800850837) (.leaf 788081504)) (.branch 112 (.leaf 775545487) (.leaf 763237535)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 751152547) (.leaf 739285563)) (.branch 116 (.leaf 727631764) (.leaf 716186462))) (.branch 119 (.branch 118 (.leaf 704945101) (.leaf 693903246)) (.branch 120 (.leaf 683056588) (.leaf 672400930)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 658).q*(generalMeanRows 658).c/2-2 = (9/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable040.value]
    have hcontinuation : (generalMeanRows 658).q*(generalMeanRows 658).cutoff/2-2 = (40/27:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable223.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7376050742) (.branch 2 (.leaf 7166607209) (.leaf 6965580287))) (.branch 5 (.branch 4 (.leaf 6772523552) (.leaf 6587021317)) (.branch 6 (.leaf 6408685875) (.leaf 6237155060)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6072090078) (.leaf 5913173568)) (.branch 10 (.leaf 5760107869) (.leaf 5612613460))) (.branch 13 (.branch 12 (.leaf 5470427562) (.leaf 5333302870)) (.branch 14 (.leaf 5201006407) (.leaf 5073318489))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4950031774) (.branch 17 (.leaf 4830950407) (.leaf 4715889232))) (.branch 20 (.branch 19 (.leaf 4604673071) (.leaf 4497136068)) (.branch 21 (.leaf 4393121079) (.leaf 4292479120)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4195068851) (.leaf 4100756103)) (.branch 25 (.leaf 4009413441) (.leaf 3920919756))) (.branch 28 (.branch 27 (.leaf 3835159894) (.leaf 3752024303)) (.branch 29 (.leaf 3671408713) (.leaf 3593213830)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3517345059) (.branch 32 (.leaf 3443712244) (.leaf 3372229416))) (.branch 35 (.branch 34 (.leaf 3302814573) (.leaf 3235389461)) (.branch 36 (.leaf 3169879376) (.leaf 3106212977)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3044322109) (.leaf 2984141638)) (.branch 40 (.leaf 2925609299) (.leaf 2868665545))) (.branch 43 (.branch 42 (.leaf 2813253413) (.leaf 2759318395)) (.branch 44 (.leaf 2706808318) (.leaf 2655673224))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2605865265) (.branch 47 (.leaf 2557338604) (.leaf 2510049312))) (.branch 50 (.branch 49 (.leaf 2463955282) (.leaf 2419016140)) (.branch 51 (.leaf 2375193165) (.leaf 2332449211)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2290748633) (.leaf 2250057221)) (.branch 55 (.leaf 2210342130) (.leaf 2171571820))) (.branch 58 (.branch 57 (.leaf 2133715997) (.leaf 2096745559)) (.branch 59 (.leaf 2060632536) (.leaf 2025350047))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1990872247) (.branch 62 (.leaf 1957174284) (.leaf 1924232256))) (.branch 65 (.branch 64 (.leaf 1892023164) (.leaf 1860524882)) (.branch 66 (.leaf 1829716111) (.leaf 1799576349)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1770085854) (.leaf 1741225613)) (.branch 70 (.leaf 1712977309) (.leaf 1685323298))) (.branch 73 (.branch 72 (.leaf 1658246572) (.leaf 1631730739)) (.branch 74 (.leaf 1605759994) (.leaf 1580319098))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1555393351) (.branch 77 (.leaf 1530968573) (.leaf 1507031079))) (.branch 80 (.branch 79 (.leaf 1483567666) (.leaf 1460565584)) (.branch 81 (.leaf 1438012525) (.leaf 1415896604)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1394206340) (.leaf 1372930639)) (.branch 85 (.leaf 1352058785) (.leaf 1331580417))) (.branch 88 (.branch 87 (.leaf 1311485522) (.leaf 1291764416)) (.branch 89 (.leaf 1272407735) (.leaf 1253406419)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1234751706) (.branch 92 (.leaf 1216435114) (.leaf 1198448434))) (.branch 95 (.branch 94 (.leaf 1180783719) (.leaf 1163433274)) (.branch 96 (.leaf 1146389647) (.leaf 1129645618)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1113194192) (.leaf 1097028591)) (.branch 100 (.leaf 1081142244) (.leaf 1065528781))) (.branch 103 (.branch 102 (.leaf 1050182024) (.leaf 1035095983)) (.branch 104 (.leaf 1020264846) (.leaf 1005682974))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 991344892) (.leaf 977245291)) (.branch 108 (.leaf 963379010) (.leaf 949741042))) (.branch 111 (.branch 110 (.leaf 936326523) (.leaf 923130726)) (.branch 112 (.leaf 910149058) (.leaf 897377058)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 884810386) (.leaf 872444826)) (.branch 116 (.leaf 860276274) (.leaf 848300742))) (.branch 119 (.branch 118 (.leaf 836514347) (.leaf 824913315)) (.branch 120 (.leaf 813493968) (.leaf 802252730)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hcontinuation : (generalMeanRows 659).q*(generalMeanRows 659).cutoff/2-2 = (166/105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable224.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6883816540) (.branch 2 (.leaf 6666203608) (.leaf 6457471109))) (.branch 5 (.branch 4 (.leaf 6257151755) (.leaf 6064810297)) (.branch 6 (.leaf 5880040661) (.leaf 5702463398)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5531723426) (.leaf 5367488011)) (.branch 10 (.leaf 5209444956) (.leaf 5057300983))) (.branch 13 (.branch 12 (.leaf 4910780265) (.leaf 4769623115)) (.branch 14 (.leaf 4633584789) (.leaf 4502434402))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4375953946) (.branch 17 (.leaf 4253937394) (.leaf 4136189876))) (.branch 20 (.branch 19 (.leaf 4022526939) (.leaf 3912773851)) (.branch 21 (.leaf 3806764977) (.leaf 3704343195)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3605359366) (.leaf 3509671835)) (.branch 25 (.leaf 3417145983) (.leaf 3327653796))) (.branch 28 (.branch 27 (.leaf 3241073484) (.leaf 3157289110)) (.branch 29 (.leaf 3076190257) (.leaf 2997671714)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2921633184) (.branch 32 (.leaf 2847979009) (.leaf 2776617921))) (.branch 35 (.branch 34 (.leaf 2707462798) (.leaf 2640430448)) (.branch 36 (.leaf 2575441395) (.leaf 2512419688)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2451292719) (.leaf 2391991045)) (.branch 40 (.leaf 2334448236) (.leaf 2278600714))) (.branch 43 (.branch 42 (.leaf 2224387616) (.leaf 2171750661)) (.branch 44 (.leaf 2120634015) (.leaf 2070984183))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2022749887) (.branch 47 (.leaf 1975881964) (.leaf 1930333265))) (.branch 50 (.branch 49 (.leaf 1886058559) (.leaf 1843014447)) (.branch 51 (.leaf 1801159270) (.leaf 1760453034)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1720857334) (.leaf 1682335279)) (.branch 55 (.leaf 1644851423) (.leaf 1608371704))) (.branch 58 (.branch 57 (.leaf 1572863379) (.leaf 1538294968)) (.branch 59 (.leaf 1504636194) (.leaf 1471857936))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1439932175) (.branch 62 (.leaf 1408831947) (.leaf 1378531298))) (.branch 65 (.branch 64 (.leaf 1349005240) (.leaf 1320229712)) (.branch 66 (.leaf 1292181539) (.leaf 1264838393)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1238178761) (.leaf 1212181911)) (.branch 70 (.leaf 1186827857) (.leaf 1162097329))) (.branch 73 (.branch 72 (.leaf 1137971744) (.leaf 1114433180)) (.branch 74 (.leaf 1091464346) (.leaf 1069048557))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1047169713) (.branch 77 (.leaf 1025812272) (.leaf 1004961227))) (.branch 80 (.branch 79 (.leaf 984602088) (.leaf 964720862)) (.branch 81 (.leaf 945304030) (.leaf 926338529)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 907811739) (.leaf 889711459)) (.branch 85 (.leaf 872025896) (.leaf 854743647))) (.branch 88 (.branch 87 (.leaf 837853685) (.leaf 821345344)) (.branch 89 (.leaf 805208307) (.leaf 789432589)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 774008529) (.branch 92 (.leaf 758926777) (.leaf 744178278))) (.branch 95 (.branch 94 (.leaf 729754268) (.leaf 715646258)) (.branch 96 (.leaf 701846026) (.leaf 688345608)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 675137286) (.leaf 662213581)) (.branch 100 (.leaf 649567246) (.leaf 637191253))) (.branch 103 (.branch 102 (.leaf 625078789) (.leaf 613223249)) (.branch 104 (.leaf 601618223) (.leaf 590257498))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 579135041) (.leaf 568245003)) (.branch 108 (.leaf 557581702) (.leaf 547139628))) (.branch 111 (.branch 110 (.leaf 536913428) (.leaf 526897905)) (.branch 112 (.leaf 517088014) (.leaf 507478852)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 498065659) (.leaf 488843807)) (.branch 116 (.leaf 479808801) (.leaf 470956273))) (.branch 119 (.branch 118 (.leaf 462281974) (.leaf 453781776)) (.branch 120 (.leaf 445451665) (.leaf 437287736)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hcontinuation : (generalMeanRows 660).q*(generalMeanRows 660).cutoff/2-2 = (166/105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable224.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6758232397) (.branch 2 (.leaf 6561563661) (.leaf 6372964384))) (.branch 5 (.branch 4 (.leaf 6191999516) (.leaf 6018264040)) (.branch 6 (.leaf 5851380306) (.leaf 5690995668)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5536780376) (.leaf 5388425695)) (.branch 10 (.leaf 5245642214) (.leaf 5108158328))) (.branch 13 (.branch 12 (.leaf 4975718869) (.leaf 4848083869)) (.branch 14 (.leaf 4725027437) (.leaf 4606336741))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4491811082) (.branch 17 (.leaf 4381261044) (.leaf 4274507727))) (.branch 20 (.branch 19 (.leaf 4171382032) (.leaf 4071724016)) (.branch 21 (.leaf 3975382295) (.leaf 3882213491)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3792081726) (.leaf 3704858159)) (.branch 25 (.leaf 3620420546) (.leaf 3538652843))) (.branch 28 (.branch 27 (.leaf 3459444835) (.leaf 3382691789)) (.branch 29 (.leaf 3308294136) (.leaf 3236157169)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3166190767) (.branch 32 (.leaf 3098309138) (.leaf 3032430573))) (.branch 35 (.branch 34 (.leaf 2968477221) (.leaf 2906374880)) (.branch 36 (.leaf 2846052797) (.leaf 2787443482)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2730482535) (.leaf 2675108484)) (.branch 40 (.leaf 2621262628) (.leaf 2568888898))) (.branch 43 (.branch 42 (.leaf 2517933719) (.leaf 2468345882)) (.branch 44 (.leaf 2420076423) (.leaf 2373078516))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2327307359) (.branch 47 (.leaf 2282720076) (.leaf 2239275625))) (.branch 50 (.branch 49 (.leaf 2196934706) (.leaf 2155659674)) (.branch 51 (.leaf 2115414465) (.leaf 2076164514)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2037876687) (.leaf 2000519214)) (.branch 55 (.leaf 1964061621) (.leaf 1928474674))) (.branch 58 (.branch 57 (.leaf 1893730316) (.leaf 1859801619)) (.branch 59 (.leaf 1826662724) (.leaf 1794288802))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1762655996) (.branch 62 (.leaf 1731741387) (.leaf 1701522946))) (.branch 65 (.branch 64 (.leaf 1671979494) (.leaf 1643090668)) (.branch 66 (.leaf 1614836881) (.leaf 1587199288)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1560159758) (.leaf 1533700837)) (.branch 70 (.leaf 1507805721) (.leaf 1482458228))) (.branch 73 (.branch 72 (.leaf 1457642771) (.leaf 1433344334)) (.branch 74 (.leaf 1409548443) (.leaf 1386241150))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1363409003) (.branch 77 (.leaf 1341039032) (.leaf 1319118725))) (.branch 80 (.branch 79 (.leaf 1297636010) (.leaf 1276579235)) (.branch 81 (.leaf 1255937154) (.leaf 1235698908)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1215854009) (.leaf 1196392326)) (.branch 85 (.leaf 1177304072) (.leaf 1158579784))) (.branch 88 (.branch 87 (.leaf 1140210318) (.leaf 1122186831)) (.branch 89 (.leaf 1104500771) (.leaf 1087143864)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1070108105) (.branch 92 (.leaf 1053385746) (.leaf 1036969287))) (.branch 95 (.branch 94 (.leaf 1020851465) (.leaf 1005025246)) (.branch 96 (.leaf 989483816) (.leaf 974220572)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 959229116) (.leaf 944503243)) (.branch 100 (.leaf 930036939) (.leaf 915824369))) (.branch 103 (.branch 102 (.leaf 901859874) (.leaf 888137962)) (.branch 104 (.leaf 874653303) (.leaf 861400724))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 848375201) (.leaf 835571854)) (.branch 108 (.leaf 822985944) (.leaf 810612866))) (.branch 111 (.branch 110 (.leaf 798448143) (.leaf 786487427)) (.branch 112 (.leaf 774726485) (.leaf 763161206)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 751787586) (.leaf 740601735)) (.branch 116 (.leaf 729599862) (.leaf 718778281))) (.branch 119 (.branch 118 (.leaf 708133401) (.leaf 697661728)) (.branch 120 (.leaf 687359856) (.leaf 677224470)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hcontinuation : (generalMeanRows 661).q*(generalMeanRows 661).cutoff/2-2 = (992/585:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable225.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6266680433) (.branch 2 (.leaf 6063974549) (.leaf 5869734859))) (.branch 5 (.branch 4 (.leaf 5683508476) (.leaf 5504873628)) (.branch 6 (.leaf 5333436894) (.leaf 5168830762)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5010711448) (.leaf 4858756940)) (.branch 10 (.leaf 4712665254) (.leaf 4572152861))) (.branch 13 (.branch 12 (.leaf 4436953270) (.leaf 4306815745)) (.branch 14 (.leaf 4181504146) (.leaf 4060795872))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3944480904) (.branch 17 (.leaf 3832360929) (.leaf 3724248538))) (.branch 20 (.branch 19 (.leaf 3619966494) (.leaf 3519347061)) (.branch 21 (.leaf 3422231386) (.leaf 3328468928)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3237916937) (.leaf 3150439968)) (.branch 25 (.leaf 3065909432) (.leaf 2984203186))) (.branch 28 (.branch 27 (.leaf 2905205143) (.leaf 2828804920)) (.branch 29 (.leaf 2754897504) (.leaf 2683382943)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2614166060) (.branch 32 (.leaf 2547156184) (.leaf 2482266899))) (.branch 35 (.branch 34 (.leaf 2419415813) (.leaf 2358524335)) (.branch 36 (.leaf 2299517473) (.leaf 2242323644)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2186874489) (.leaf 2133104708)) (.branch 40 (.leaf 2080951900) (.leaf 2030356415))) (.branch 43 (.branch 42 (.leaf 1981261213) (.leaf 1933611731)) (.branch 44 (.leaf 1887355762) (.leaf 1842443335))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1798826605) (.branch 47 (.leaf 1756459750) (.leaf 1715298874))) (.branch 50 (.branch 49 (.leaf 1675301908) (.leaf 1636428530)) (.branch 51 (.leaf 1598640077) (.leaf 1561899470)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1526171134) (.leaf 1491420936)) (.branch 55 (.leaf 1457616109) (.leaf 1424725197))) (.branch 58 (.branch 57 (.leaf 1392717992) (.leaf 1361565475)) (.branch 59 (.leaf 1331239765) (.leaf 1301714067))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1272962624) (.branch 62 (.leaf 1244960670) (.leaf 1217684386))) (.branch 65 (.branch 64 (.leaf 1191110862) (.leaf 1165218049)) (.branch 66 (.leaf 1139984731) (.leaf 1115390485)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1091415643) (.leaf 1068041267)) (.branch 70 (.leaf 1045249114) (.leaf 1023021605))) (.branch 73 (.branch 72 (.leaf 1001341801) (.leaf 980193373)) (.branch 74 (.leaf 959560578) (.leaf 939428237))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 919781705) (.branch 77 (.leaf 900606856) (.leaf 881890058))) (.branch 80 (.branch 79 (.leaf 863618156) (.leaf 845778448)) (.branch 81 (.leaf 828358672) (.leaf 811346984)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 794731944) (.leaf 778502500)) (.branch 85 (.leaf 762647970) (.leaf 747158032))) (.branch 88 (.branch 87 (.leaf 732022705) (.leaf 717232340)) (.branch 89 (.leaf 702777603) (.leaf 688649467)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 674839197) (.branch 92 (.leaf 661338341) (.leaf 648138719))) (.branch 95 (.branch 94 (.leaf 635232412) (.leaf 622611750)) (.branch 96 (.leaf 610269307) (.leaf 598197892)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 586390534) (.leaf 574840482)) (.branch 100 (.leaf 563541190) (.leaf 552486316))) (.branch 103 (.branch 102 (.leaf 541669707) (.leaf 531085401)) (.branch 104 (.leaf 520727611) (.leaf 510590728))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 500669307) (.leaf 490958063)) (.branch 108 (.leaf 481451870) (.leaf 472145750))) (.branch 111 (.branch 110 (.leaf 463034870) (.leaf 454114536)) (.branch 112 (.leaf 445380190) (.leaf 436827405)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 428451878) (.leaf 420249428)) (.branch 116 (.leaf 412215994) (.leaf 404347624))) (.branch 119 (.branch 118 (.leaf 396640480) (.leaf 389090828)) (.branch 120 (.leaf 381695037) (.leaf 374449574)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 662).q*(generalMeanRows 662).c/2-2 = (357/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable067.value]
    have hcontinuation : (generalMeanRows 662).q*(generalMeanRows 662).cutoff/2-2 = (992/585:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable225.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5991209708) (.branch 2 (.leaf 5796657210) (.leaf 5610313045))) (.branch 5 (.branch 4 (.leaf 5431733802) (.leaf 5260506612)) (.branch 6 (.leaf 5096246459) (.leaf 4938593783)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4787212345) (.leaf 4641787314)) (.branch 10 (.leaf 4502023554) (.leaf 4367644080))) (.branch 13 (.branch 12 (.leaf 4238388667) (.leaf 4114012588)) (.branch 14 (.leaf 3994285478) (.leaf 3878990288))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3767922349) (.branch 17 (.leaf 3660888503) (.leaf 3557706318))) (.branch 20 (.branch 19 (.leaf 3458203363) (.leaf 3362216548)) (.branch 21 (.leaf 3269591512) (.leaf 3180182065)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3093849665) (.leaf 3010462947)) (.branch 25 (.leaf 2929897274) (.leaf 2852034334))) (.branch 28 (.branch 27 (.leaf 2776761756) (.leaf 2703972757)) (.branch 29 (.leaf 2633565821) (.leaf 2565444386)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2499516564) (.branch 32 (.leaf 2435694877) (.leaf 2373896008))) (.branch 35 (.branch 34 (.leaf 2314040570) (.leaf 2256052893)) (.branch 36 (.leaf 2199860817) (.leaf 2145395508)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2092591275) (.leaf 2041385408)) (.branch 40 (.leaf 1991718022) (.leaf 1943531904))) (.branch 43 (.branch 42 (.leaf 1896772383) (.leaf 1851387193)) (.branch 44 (.leaf 1807326357) (.leaf 1764542066))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1722988575) (.branch 47 (.leaf 1682622098) (.leaf 1643400712))) (.branch 50 (.branch 49 (.leaf 1605284266) (.leaf 1568234296)) (.branch 51 (.leaf 1532213942) (.leaf 1497187869)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1463122200) (.leaf 1429984443)) (.branch 55 (.leaf 1397743425) (.leaf 1366369235))) (.branch 58 (.branch 57 (.leaf 1335833158) (.leaf 1306107629)) (.branch 59 (.leaf 1277166172) (.leaf 1248983354))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1221534738) (.branch 62 (.leaf 1194796836) (.leaf 1168747071))) (.branch 65 (.branch 64 (.leaf 1143363729) (.leaf 1118625927)) (.branch 66 (.leaf 1094513573) (.leaf 1071007334)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1048088600) (.leaf 1025739455)) (.branch 70 (.leaf 1003942643) (.leaf 982681547))) (.branch 73 (.branch 72 (.leaf 961940154) (.leaf 941703034)) (.branch 74 (.leaf 921955313) (.leaf 902682652))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 883871221) (.branch 77 (.leaf 865507683) (.leaf 847579167))) (.branch 80 (.branch 79 (.leaf 830073256) (.leaf 812977962)) (.branch 81 (.leaf 796281713) (.leaf 779973334)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 764042030) (.leaf 748477375)) (.branch 85 (.leaf 733269291) (.leaf 718408041))) (.branch 88 (.branch 87 (.leaf 703884209) (.leaf 689688692)) (.branch 89 (.leaf 675812687) (.leaf 662247677)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 648985422) (.branch 92 (.leaf 636017948) (.leaf 623337537))) (.branch 95 (.branch 94 (.leaf 610936716) (.leaf 598808249)) (.branch 96 (.leaf 586945128) (.leaf 575340563)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 563987977) (.leaf 552880992)) (.branch 100 (.leaf 542013431) (.leaf 531379302))) (.branch 103 (.branch 102 (.leaf 520972794) (.leaf 510788274)) (.branch 104 (.leaf 500820275) (.leaf 491063492))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 481512781) (.leaf 472163144)) (.branch 108 (.leaf 463009731) (.leaf 454047835))) (.branch 111 (.branch 110 (.leaf 445272880) (.leaf 436680426)) (.branch 112 (.leaf 428266155) (.leaf 420025875)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 411955511) (.leaf 404051100)) (.branch 116 (.leaf 396308790) (.leaf 388724839))) (.branch 119 (.branch 118 (.leaf 381295602) (.leaf 374017538)) (.branch 120 (.leaf 366887201) (.leaf 359901236)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 663).q*(generalMeanRows 663).c/2-2 = (289/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable093.value]
    have hcontinuation : (generalMeanRows 663).q*(generalMeanRows 663).cutoff/2-2 = (44/25:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable226.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5819887478) (.branch 2 (.leaf 5633441871) (.leaf 5454911331))) (.branch 5 (.branch 4 (.leaf 5283863282) (.leaf 5119895090)) (.branch 6 (.leaf 4962631440) (.leaf 4811721984)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4666839257) (.leaf 4527676804)) (.branch 10 (.leaf 4393947499) (.leaf 4265382033))) (.branch 13 (.branch 12 (.leaf 4141727545) (.leaf 4022746387)) (.branch 14 (.leaf 3908215002) (.leaf 3797922905))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3691671750) (.branch 17 (.leaf 3589274486) (.leaf 3490554575))) (.branch 20 (.branch 19 (.leaf 3395345286) (.leaf 3303489041)) (.branch 21 (.leaf 3214836808) (.leaf 3129247559)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3046587750) (.leaf 2966730854)) (.branch 25 (.leaf 2889556924) (.leaf 2814952194))) (.branch 28 (.branch 27 (.leaf 2742808695) (.leaf 2673023917)) (.branch 29 (.leaf 2605500481) (.leaf 2540145841)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2476872001) (.branch 32 (.leaf 2415595256) (.leaf 2356235951))) (.branch 35 (.branch 34 (.leaf 2298718247) (.leaf 2242969917)) (.branch 36 (.leaf 2188922138) (.leaf 2136509312)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2085668887) (.leaf 2036341197)) (.branch 40 (.leaf 1988469304) (.leaf 1941998858))) (.branch 43 (.branch 42 (.leaf 1896877957) (.leaf 1853057024)) (.branch 44 (.leaf 1810488686) (.leaf 1769127657))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1728930638) (.branch 47 (.leaf 1689856212) (.leaf 1651864753))) (.branch 50 (.branch 49 (.leaf 1614918332) (.leaf 1578980640)) (.branch 51 (.leaf 1544016900) (.leaf 1509993801)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1476879420) (.leaf 1444643158)) (.branch 55 (.leaf 1413255675) (.leaf 1382688834))) (.branch 58 (.branch 57 (.leaf 1352915639) (.leaf 1323910183)) (.branch 59 (.leaf 1295647599) (.leaf 1268104010))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1241256482) (.branch 62 (.leaf 1215082984) (.leaf 1189562343))) (.branch 65 (.branch 64 (.leaf 1164674208) (.leaf 1140399011)) (.branch 66 (.leaf 1116717931) (.leaf 1093612865)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1071066390) (.leaf 1049061738)) (.branch 70 (.leaf 1027582764) (.leaf 1006613921))) (.branch 73 (.branch 72 (.leaf 986140231) (.leaf 966147265)) (.branch 74 (.leaf 946621114) (.leaf 927548371))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 908916107) (.branch 77 (.leaf 890711853) (.leaf 872923579))) (.branch 80 (.branch 79 (.leaf 855539675) (.leaf 838548937)) (.branch 81 (.leaf 821940544) (.leaf 805704050)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 789829361) (.leaf 774306728)) (.branch 85 (.leaf 759126725) (.leaf 744280244))) (.branch 88 (.branch 87 (.leaf 729758476) (.leaf 715552904)) (.branch 89 (.leaf 701655286) (.leaf 688057650)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 674752278) (.branch 92 (.leaf 661731702) (.leaf 648988688))) (.branch 95 (.branch 94 (.leaf 636516231) (.leaf 624307546)) (.branch 96 (.leaf 612356058) (.leaf 600655396)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 589199382) (.leaf 577982029)) (.branch 100 (.leaf 566997528) (.leaf 556240247))) (.branch 103 (.branch 102 (.leaf 545704720) (.leaf 535385643)) (.branch 104 (.leaf 525277869) (.leaf 515376401))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 505676385) (.leaf 496173110)) (.branch 108 (.leaf 486861996) (.leaf 477738596))) (.branch 111 (.branch 110 (.leaf 468798587) (.leaf 460037767)) (.branch 112 (.leaf 451452053) (.leaf 443037472)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 434790161) (.leaf 426706364)) (.branch 116 (.leaf 418782425) (.leaf 411014787))) (.branch 119 (.branch 118 (.leaf 403399988) (.leaf 395934658)) (.branch 120 (.leaf 388615517) (.leaf 381439369)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 664).q*(generalMeanRows 664).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5704062489) (.branch 2 (.leaf 5525904657) (.leaf 5355340127))) (.branch 5 (.branch 4 (.leaf 5191948246) (.leaf 5035337679)) (.branch 6 (.leaf 4885143842) (.leaf 4741026612)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4602668286) (.leaf 4469771743)) (.branch 10 (.leaf 4342058801) (.leaf 4219268732))) (.branch 13 (.branch 12 (.leaf 4101156924) (.leaf 3987493662)) (.branch 14 (.leaf 3878063031) (.leaf 3772661911))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3671099064) (.branch 17 (.leaf 3573194298) (.leaf 3478777705))) (.branch 20 (.branch 19 (.leaf 3387688961) (.leaf 3299776682)) (.branch 21 (.leaf 3214897832) (.leaf 3132917181)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3053706800) (.leaf 2977145599)) (.branch 25 (.leaf 2903118897) (.leaf 2831518025))) (.branch 28 (.branch 27 (.leaf 2762239956) (.leaf 2695186965)) (.branch 29 (.leaf 2630266310) (.leaf 2567389935)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2506474199) (.branch 32 (.leaf 2447439615) (.leaf 2390210612))) (.branch 35 (.branch 34 (.leaf 2334715314) (.leaf 2280885326)) (.branch 36 (.leaf 2228655545) (.leaf 2177963971)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2128751541) (.leaf 2080961966)) (.branch 40 (.leaf 2034541580) (.leaf 1989439202))) (.branch 43 (.branch 42 (.leaf 1945605998) (.leaf 1902995363)) (.branch 44 (.leaf 1861562797) (.leaf 1821265803))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1782063773) (.branch 47 (.leaf 1743917902) (.leaf 1706791085))) (.branch 50 (.branch 49 (.leaf 1670647839) (.leaf 1635454214)) (.branch 51 (.leaf 1601177724) (.leaf 1567787266)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1535253055) (.leaf 1503546562)) (.branch 55 (.leaf 1472640447) (.leaf 1442508505))) (.branch 58 (.branch 57 (.leaf 1413125608) (.leaf 1384467657)) (.branch 59 (.leaf 1356511530) (.leaf 1329235036))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1302616871) (.branch 62 (.leaf 1276636579) (.leaf 1251274506))) (.branch 65 (.branch 64 (.leaf 1226511771) (.leaf 1202330223)) (.branch 66 (.leaf 1178712412) (.leaf 1155641555)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1133101505) (.leaf 1111076727)) (.branch 70 (.leaf 1089552263) (.leaf 1068513712))) (.branch 73 (.branch 72 (.leaf 1047947205) (.leaf 1027839376)) (.branch 74 (.leaf 1008177349) (.leaf 988948706))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 970141478) (.branch 77 (.leaf 951744117) (.leaf 933745481))) (.branch 80 (.branch 79 (.leaf 916134820) (.leaf 898901752)) (.branch 81 (.leaf 882036255) (.leaf 865528647)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 849369574) (.leaf 833549997)) (.branch 85 (.leaf 818061175) (.leaf 802894660))) (.branch 88 (.branch 87 (.leaf 788042276) (.leaf 773496116)) (.branch 89 (.leaf 759248527) (.leaf 745292101)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 731619665) (.branch 92 (.leaf 718224273) (.leaf 705099194))) (.branch 95 (.branch 94 (.leaf 692237906) (.leaf 679634089)) (.branch 96 (.leaf 667281613) (.leaf 655174538)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 643307096) (.leaf 631673697)) (.branch 100 (.leaf 620268912) (.leaf 609087473))) (.branch 103 (.branch 102 (.leaf 598124264) (.leaf 587374317)) (.branch 104 (.leaf 576832807) (.leaf 566495044))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 556356474) (.leaf 546412666)) (.branch 108 (.leaf 536659314) (.leaf 527092230))) (.branch 111 (.branch 110 (.leaf 517707342) (.leaf 508500687)) (.branch 112 (.leaf 499468408) (.leaf 490606752)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 481912065) (.leaf 473380791)) (.branch 116 (.leaf 465009464) (.leaf 456794710))) (.branch 119 (.branch 118 (.leaf 448733241) (.leaf 440821852)) (.branch 120 (.leaf 433057422) (.leaf 425436907)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 665).q*(generalMeanRows 665).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5261277176) (.branch 2 (.leaf 5086424835) (.leaf 4919165256))) (.branch 5 (.branch 4 (.leaf 4759076957) (.leaf 4605767816)) (.branch 6 (.leaf 4458872505) (.leaf 4318050199)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4182982533) (.leaf 4053371767)) (.branch 10 (.leaf 3928939141) (.leaf 3809423382))) (.branch 13 (.branch 12 (.leaf 3694579373) (.leaf 3584176924)) (.branch 14 (.leaf 3477999677) (.leaf 3375844100))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3277518566) (.branch 17 (.leaf 3182842522) (.leaf 3091645721))) (.branch 20 (.branch 19 (.leaf 3003767518) (.leaf 2919056229)) (.branch 21 (.leaf 2837368537) (.leaf 2758568943)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2682529266) (.leaf 2609128176)) (.branch 25 (.leaf 2538250762) (.leaf 2469788138))) (.branch 28 (.branch 27 (.leaf 2403637067) (.leaf 2339699625)) (.branch 29 (.leaf 2277882876) (.leaf 2218098579)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2160262913) (.branch 32 (.leaf 2104296217) (.leaf 2050122751))) (.branch 35 (.branch 34 (.leaf 1997670473) (.leaf 1946870829)) (.branch 36 (.leaf 1897658557) (.leaf 1849971506)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1803750460) (.leaf 1758938982)) (.branch 40 (.leaf 1715483264) (.leaf 1673331978))) (.branch 43 (.branch 42 (.leaf 1632436154) (.leaf 1592749046)) (.branch 44 (.leaf 1554226021) (.leaf 1516824445))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1480503581) (.branch 47 (.leaf 1445224492) (.leaf 1410949948))) (.branch 50 (.branch 49 (.leaf 1377644338) (.leaf 1345273591)) (.branch 51 (.leaf 1313805097) (.leaf 1283207634)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1253451302) (.leaf 1224507455)) (.branch 55 (.leaf 1196348641) (.leaf 1168948545))) (.branch 58 (.branch 57 (.leaf 1142281930) (.leaf 1116324592)) (.branch 59 (.leaf 1091053306) (.leaf 1066445780))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1042480613) (.branch 62 (.leaf 1019137253) (.leaf 996395954))) (.branch 65 (.branch 64 (.leaf 974237745) (.leaf 952644389)) (.branch 66 (.leaf 931598351) (.leaf 911082767)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 891081414) (.leaf 871578680)) (.branch 70 (.leaf 852559537) (.leaf 834009515))) (.branch 73 (.branch 72 (.leaf 815914679) (.leaf 798261602)) (.branch 74 (.leaf 781037346) (.leaf 764229443))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 747825866) (.branch 77 (.leaf 731815021) (.leaf 716185720))) (.branch 80 (.branch 79 (.leaf 700927169) (.leaf 686028949)) (.branch 81 (.leaf 671481002) (.leaf 657273613)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643397399) (.leaf 629843295)) (.branch 85 (.leaf 616602540) (.leaf 603666663))) (.branch 88 (.branch 87 (.leaf 591027475) (.leaf 578677056)) (.branch 89 (.leaf 566607744) (.leaf 554812126)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543283024) (.branch 92 (.leaf 532013494) (.leaf 520996808))) (.branch 95 (.branch 94 (.leaf 510226451) (.leaf 499696113)) (.branch 96 (.leaf 489399678) (.leaf 479331218)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 469484989) (.leaf 459855419)) (.branch 100 (.leaf 450437105) (.leaf 441224807))) (.branch 103 (.branch 102 (.leaf 432213438) (.leaf 423398065)) (.branch 104 (.leaf 414773897) (.leaf 406336285))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 398080712) (.leaf 390002794)) (.branch 108 (.leaf 382098269) (.leaf 374363000))) (.branch 111 (.branch 110 (.leaf 366792964) (.leaf 359384251)) (.branch 112 (.leaf 352133060) (.leaf 345035697)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 338088568) (.leaf 331288177)) (.branch 116 (.leaf 324631123) (.leaf 318114099))) (.branch 119 (.branch 118 (.leaf 311733885) (.leaf 305487347)) (.branch 120 (.leaf 299371433) (.leaf 293383175)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 666).q*(generalMeanRows 666).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5270107067) (.branch 2 (.leaf 5097070189) (.leaf 4931580446))) (.branch 5 (.branch 4 (.leaf 4773214886) (.leaf 4621580175)) (.branch 6 (.leaf 4476310007) (.leaf 4337062797)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4203519618) (.leaf 4075382351)) (.branch 10 (.leaf 3952372020) (.leaf 3834227293))) (.branch 13 (.branch 12 (.leaf 3720703122) (.leaf 3611569520)) (.branch 14 (.leaf 3506610436) (.leaf 3405622749))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3308415334) (.branch 17 (.leaf 3214808219) (.leaf 3124631809))) (.branch 20 (.branch 19 (.leaf 3037726178) (.leaf 2953940413)) (.branch 21 (.leaf 2873132019) (.leaf 2795166360)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2719916154) (.leaf 2647261002)) (.branch 25 (.leaf 2577086949) (.leaf 2509286085))) (.branch 28 (.branch 27 (.leaf 2443756168) (.leaf 2380400279)) (.branch 29 (.leaf 2319126498) (.leaf 2259847607)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2202480807) (.branch 32 (.leaf 2146947465) (.leaf 2093172862))) (.branch 35 (.branch 34 (.leaf 2041085976) (.leaf 1990619264)) (.branch 36 (.leaf 1941708471) (.leaf 1894292439)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1848312937) (.leaf 1803714500)) (.branch 40 (.leaf 1760444276) (.leaf 1718451884))) (.branch 43 (.branch 42 (.leaf 1677689279) (.leaf 1638110631)) (.branch 44 (.leaf 1599672200) (.leaf 1562332233))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1526050853) (.branch 47 (.leaf 1490789966) (.leaf 1456513165))) (.branch 50 (.branch 49 (.leaf 1423185648) (.leaf 1390774130)) (.branch 51 (.leaf 1359246769) (.leaf 1328573094)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1298723935) (.leaf 1269671358)) (.branch 55 (.leaf 1241388604) (.leaf 1213850032))) (.branch 58 (.branch 57 (.leaf 1187031063) (.leaf 1160908128)) (.branch 59 (.leaf 1135458623) (.leaf 1110660857))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1086494013) (.branch 62 (.leaf 1062938104) (.leaf 1039973935))) (.branch 65 (.branch 64 (.leaf 1017583065) (.leaf 995747773)) (.branch 66 (.leaf 974451024) (.leaf 953676436)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 933408255) (.leaf 913631320)) (.branch 70 (.leaf 894331039) (.leaf 875493365))) (.branch 73 (.branch 72 (.leaf 857104771) (.leaf 839152225)) (.branch 74 (.leaf 821623168) (.leaf 804505498))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 787787543) (.branch 77 (.leaf 771458049) (.leaf 755506158))) (.branch 80 (.branch 79 (.leaf 739921391) (.leaf 724693634)) (.branch 81 (.leaf 709813122) (.leaf 695270424)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 681056427) (.leaf 667162328)) (.branch 85 (.leaf 653579614) (.leaf 640300059))) (.branch 88 (.branch 87 (.leaf 627315703) (.leaf 614618848)) (.branch 89 (.leaf 602202046) (.leaf 590058086)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 578179988) (.branch 92 (.leaf 566560994) (.leaf 555194557))) (.branch 95 (.branch 94 (.leaf 544074333) (.leaf 533194176)) (.branch 96 (.leaf 522548128) (.leaf 512130411)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 501935423) (.leaf 491957730)) (.branch 100 (.leaf 482192060) (.leaf 472633296))) (.branch 103 (.branch 102 (.leaf 463276471) (.leaf 454116764)) (.branch 104 (.leaf 445149491) (.leaf 436370105))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 427774187) (.leaf 419357443)) (.branch 108 (.leaf 411115700) (.leaf 403044902))) (.branch 111 (.branch 110 (.leaf 395141104) (.leaf 387400471)) (.branch 112 (.leaf 379819272) (.leaf 372393877)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 365120753) (.leaf 357996465)) (.branch 116 (.leaf 351017666) (.leaf 344181098))) (.branch 119 (.branch 118 (.leaf 337483589) (.leaf 330922052)) (.branch 120 (.leaf 324493476) (.leaf 318194930)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 667).q*(generalMeanRows 667).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5284790399) (.branch 2 (.leaf 5115778568) (.leaf 4954124743))) (.branch 5 (.branch 4 (.leaf 4799413224) (.leaf 4651257580)) (.branch 6 (.leaf 4509298090) (.leaf 4373199466)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4242648809) (.leaf 4117353780)) (.branch 10 (.leaf 3997040950) (.leaf 3881454322))) (.branch 13 (.branch 12 (.leaf 3770353980) (.leaf 3663514876)) (.branch 14 (.leaf 3560725724) (.leaf 3461787992))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3366514986) (.branch 17 (.leaf 3274731011) (.leaf 3186270601))) (.branch 20 (.branch 19 (.leaf 3100977817) (.leaf 3018705602)) (.branch 21 (.leaf 2939315184) (.leaf 2862675527)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2788662831) (.leaf 2717160061)) (.branch 25 (.leaf 2648056517) (.leaf 2581247434))) (.branch 28 (.branch 27 (.leaf 2516633613) (.leaf 2454121077)) (.branch 29 (.leaf 2393620752) (.leaf 2335048171)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2278323196) (.branch 32 (.leaf 2223369764) (.leaf 2170115645))) (.branch 35 (.branch 34 (.leaf 2118492219) (.leaf 2068434268)) (.branch 36 (.leaf 2019879782) (.leaf 1972769774)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1927048111) (.leaf 1882661354)) (.branch 40 (.leaf 1839558610) (.leaf 1797691389))) (.branch 43 (.branch 42 (.leaf 1757013473) (.leaf 1717480796)) (.branch 44 (.leaf 1679051321) (.leaf 1641684940))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1605343364) (.branch 47 (.leaf 1569990031) (.leaf 1535590015))) (.branch 50 (.branch 49 (.leaf 1502109937) (.leaf 1469517891)) (.branch 51 (.leaf 1437783362) (.leaf 1406877161)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1376771352) (.leaf 1347439191)) (.branch 55 (.leaf 1318855068) (.leaf 1290994446))) (.branch 58 (.branch 57 (.leaf 1263833814) (.leaf 1237350631)) (.branch 59 (.leaf 1211523279) (.leaf 1186331022))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1161753961) (.branch 62 (.leaf 1137772992) (.leaf 1114369770))) (.branch 65 (.branch 64 (.leaf 1091526673) (.leaf 1069226767)) (.branch 66 (.leaf 1047453776) (.leaf 1026192048)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1005426526) (.leaf 985142726)) (.branch 70 (.leaf 965326703) (.leaf 945965034))) (.branch 73 (.branch 72 (.leaf 927044789) (.leaf 908553510)) (.branch 74 (.leaf 890479192) (.leaf 872810262))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 855535557) (.branch 77 (.leaf 838644311) (.leaf 822126135))) (.branch 80 (.branch 79 (.leaf 805971000) (.leaf 790169222)) (.branch 81 (.leaf 774711450) (.leaf 759588649)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 744792085) (.leaf 730313318)) (.branch 85 (.leaf 716144184) (.leaf 702276790))) (.branch 88 (.branch 87 (.leaf 688703494) (.leaf 675416904)) (.branch 89 (.leaf 662409863) (.leaf 649675438)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 637206917) (.branch 92 (.leaf 624997794) (.leaf 613041765))) (.branch 95 (.branch 94 (.leaf 601332719) (.leaf 589864730)) (.branch 96 (.leaf 578632049) (.leaf 567629101)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 556850474) (.leaf 546290915)) (.branch 100 (.leaf 535945325) (.leaf 525808751))) (.branch 103 (.branch 102 (.leaf 515876382) (.leaf 506143545)) (.branch 104 (.leaf 496605696) (.leaf 487258421))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 478097427) (.leaf 469118539)) (.branch 108 (.leaf 460317697) (.leaf 451690949))) (.branch 111 (.branch 110 (.leaf 443234452) (.leaf 434944464)) (.branch 112 (.leaf 426817343) (.leaf 418849541)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 411037605) (.leaf 403378171)) (.branch 116 (.leaf 395867960) (.leaf 388503779))) (.branch 119 (.branch 118 (.leaf 381282515) (.leaf 374201134)) (.branch 120 (.leaf 367256676) (.leaf 360446258)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 668).q*(generalMeanRows 668).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 668).q*(generalMeanRows 668).cutoff/2-2 = (1990/979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable227.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5541897390) (.branch 2 (.leaf 5370095887) (.leaf 5205671086))) (.branch 5 (.branch 4 (.leaf 5048208921) (.leaf 4897324397)) (.branch 6 (.leaf 4752659053) (.leaf 4613878686)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4480671329) (.leaf 4352745434)) (.branch 10 (.leaf 4229828232) (.leaf 4111664264))) (.branch 13 (.branch 12 (.leaf 3998014047) (.leaf 3888652865)) (.branch 14 (.leaf 3783369674) (.leaf 3681966105))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3584255549) (.branch 17 (.leaf 3490062335) (.leaf 3399220959))) (.branch 20 (.branch 19 (.leaf 3311575394) (.leaf 3226978445)) (.branch 21 (.leaf 3145291161) (.leaf 3066382293)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2990127792) (.leaf 2916410349)) (.branch 25 (.leaf 2845118964) (.leaf 2776148553))) (.branch 28 (.branch 27 (.leaf 2709399580) (.leaf 2644777715)) (.branch 29 (.leaf 2582193520) (.leaf 2521562154)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2462803099) (.branch 32 (.leaf 2405839905) (.leaf 2350599950))) (.branch 35 (.branch 34 (.leaf 2297014224) (.leaf 2245017116)) (.branch 36 (.leaf 2194546222) (.leaf 2145542164)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2097948421) (.leaf 2051711170)) (.branch 40 (.leaf 2006779136) (.leaf 1963103455))) (.branch 43 (.branch 42 (.leaf 1920637540) (.leaf 1879336959)) (.branch 44 (.leaf 1839159321) (.leaf 1800064165))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1762012861) (.branch 47 (.leaf 1724968510) (.leaf 1688895859))) (.branch 50 (.branch 49 (.leaf 1653761209) (.leaf 1619532341)) (.branch 51 (.leaf 1586178438) (.leaf 1553670012)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1521978839) (.leaf 1491077897)) (.branch 55 (.leaf 1460941300) (.leaf 1431544250))) (.branch 58 (.branch 57 (.leaf 1402862976) (.leaf 1374874689)) (.branch 59 (.leaf 1347557529) (.leaf 1320890526))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1294853552) (.branch 62 (.leaf 1269427284) (.leaf 1244593163))) (.branch 65 (.branch 64 (.leaf 1220333361) (.leaf 1196630743)) (.branch 66 (.leaf 1173468839) (.leaf 1150831809)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1128704415) (.leaf 1107071996)) (.branch 70 (.leaf 1085920439) (.leaf 1065236152))) (.branch 73 (.branch 72 (.leaf 1045006047) (.leaf 1025217512)) (.branch 74 (.leaf 1005858391) (.leaf 986916965))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 968381933) (.branch 77 (.leaf 950242389) (.leaf 932487813))) (.branch 80 (.branch 79 (.leaf 915108048) (.leaf 898093285)) (.branch 81 (.leaf 881434052) (.leaf 865121196)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 849145869) (.leaf 833499520)) (.branch 85 (.leaf 818173879) (.leaf 803160944))) (.branch 88 (.branch 87 (.leaf 788452973) (.leaf 774042475)) (.branch 89 (.leaf 759922193) (.leaf 746085102)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 732524396) (.branch 92 (.leaf 719233479) (.leaf 706205959))) (.branch 95 (.branch 94 (.leaf 693435638) (.leaf 680916505)) (.branch 96 (.leaf 668642729) (.leaf 656608653)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 644808786) (.leaf 633237796)) (.branch 100 (.leaf 621890508) (.leaf 610761893))) (.branch 103 (.branch 102 (.leaf 599847066) (.leaf 589141280)) (.branch 104 (.leaf 578639920) (.leaf 568338501))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 558232659) (.leaf 548318151)) (.branch 108 (.leaf 538590848) (.leaf 529046731))) (.branch 111 (.branch 110 (.leaf 519681890) (.leaf 510492516)) (.branch 112 (.leaf 501474903) (.leaf 492625439)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 483940606) (.leaf 475416976)) (.branch 116 (.leaf 467051207) (.leaf 458840044))) (.branch 119 (.branch 118 (.leaf 450780311) (.leaf 442868913)) (.branch 120 (.leaf 435102829) (.leaf 427479115)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 669).q*(generalMeanRows 669).c/2-2 = (271/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable076.value]
    have hcontinuation : (generalMeanRows 669).q*(generalMeanRows 669).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5095494538) (.branch 2 (.leaf 4923269259) (.leaf 4758591192))) (.branch 5 (.branch 4 (.leaf 4601039096) (.leaf 4450221140)) (.branch 6 (.leaf 4305772340) (.leaf 4167352264)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4034642986) (.leaf 3907347249)) (.branch 10 (.leaf 3785186813) (.leaf 3667900965))) (.branch 13 (.branch 12 (.leaf 3555245174) (.leaf 3446989872)) (.branch 14 (.leaf 3342919343) (.leaf 3242830719))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3146533056) (.branch 17 (.leaf 3053846501) (.leaf 2964601515))) (.branch 20 (.branch 19 (.leaf 2878638176) (.leaf 2795805527)) (.branch 21 (.leaf 2715960981) (.leaf 2638969775)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2564704464) (.leaf 2493044450)) (.branch 25 (.leaf 2423875554) (.leaf 2357089615))) (.branch 28 (.branch 27 (.leaf 2292584119) (.leaf 2230261852)) (.branch 29 (.leaf 2170030586) (.leaf 2111802775)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2055495284) (.branch 32 (.leaf 2001029126) (.leaf 1948329227))) (.branch 35 (.branch 34 (.leaf 1897324195) (.leaf 1847946115)) (.branch 36 (.leaf 1800130353) (.leaf 1753815370)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1708942550) (.leaf 1665456044)) (.branch 40 (.leaf 1623302613) (.leaf 1582431490))) (.branch 43 (.branch 42 (.leaf 1542794248) (.leaf 1504344673)) (.branch 44 (.leaf 1467038647) (.leaf 1430834040))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1395690604) (.branch 47 (.leaf 1361569879) (.leaf 1328435094))) (.branch 50 (.branch 49 (.leaf 1296251089) (.leaf 1264984229)) (.branch 51 (.leaf 1234602326) (.leaf 1205074570)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1176371457) (.leaf 1148464729)) (.branch 55 (.leaf 1121327306) (.leaf 1094933236))) (.branch 58 (.branch 57 (.leaf 1069257634) (.leaf 1044276636)) (.branch 59 (.leaf 1019967345) (.leaf 996307790))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 973276877) (.branch 62 (.leaf 950854352) (.leaf 929020761))) (.branch 65 (.branch 64 (.leaf 907757410) (.leaf 887046332)) (.branch 66 (.leaf 866870257) (.leaf 847212572)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 828057301) (.leaf 809389067)) (.branch 70 (.leaf 791193072) (.leaf 773455068))) (.branch 73 (.branch 72 (.leaf 756161335) (.leaf 739298654)) (.branch 74 (.leaf 722854288) (.leaf 706815963))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 691171842) (.branch 77 (.leaf 675910510) (.leaf 661020959))) (.branch 80 (.branch 79 (.leaf 646492565) (.leaf 632315074)) (.branch 81 (.leaf 618478588) (.leaf 604973548)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 591790723) (.leaf 578921192)) (.branch 85 (.leaf 566356335) (.leaf 554087822))) (.branch 88 (.branch 87 (.leaf 542107595) (.leaf 530407863)) (.branch 89 (.leaf 518981091) (.leaf 507819987)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 496917492) (.branch 92 (.leaf 486266777) (.leaf 475861227))) (.branch 95 (.branch 94 (.leaf 465694436) (.leaf 455760199)) (.branch 96 (.leaf 446052504) (.leaf 436565525)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 427293613) (.leaf 418231295)) (.branch 100 (.leaf 409373259) (.leaf 400714356))) (.branch 103 (.branch 102 (.leaf 392249590) (.leaf 383974112)) (.branch 104 (.leaf 375883218) (.leaf 367972340))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360237044) (.leaf 352673023)) (.branch 108 (.leaf 345276096) (.leaf 338042198))) (.branch 111 (.branch 110 (.leaf 330967383) (.leaf 324047814)) (.branch 112 (.leaf 317279761) (.leaf 310659600)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 304183806) (.leaf 297848952)) (.branch 116 (.leaf 291651702) (.leaf 285588816))) (.branch 119 (.branch 118 (.leaf 279657136) (.leaf 273853592)) (.branch 120 (.leaf 268175197) (.leaf 262619040)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 670).q*(generalMeanRows 670).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 670).q*(generalMeanRows 670).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5101290695) (.branch 2 (.leaf 4930932365) (.leaf 4768068475))) (.branch 5 (.branch 4 (.leaf 4612276797) (.leaf 4463164748)) (.branch 6 (.leaf 4320366805) (.leaf 4183542189)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4052372808) (.leaf 3926561397)) (.branch 10 (.leaf 3805829856) (.leaf 3689917745))) (.branch 13 (.branch 12 (.leaf 3578580924) (.leaf 3471590324)) (.branch 14 (.leaf 3368730822) (.leaf 3269800231))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3174608363) (.branch 17 (.leaf 3082976185) (.leaf 2994735039))) (.branch 20 (.branch 19 (.leaf 2909725932) (.leaf 2827798882)) (.branch 21 (.leaf 2748812314) (.leaf 2672632505)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2599133077) (.leaf 2528194522)) (.branch 25 (.leaf 2459703764) (.leaf 2393553756))) (.branch 28 (.branch 27 (.leaf 2329643108) (.leaf 2267875735)) (.branch 29 (.leaf 2208160536) (.leaf 2150411093)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2094545393) (.branch 32 (.leaf 2040485568) (.leaf 1988157650))) (.branch 35 (.branch 34 (.leaf 1937491344) (.leaf 1888419823)) (.branch 36 (.leaf 1840879521) (.leaf 1794809958)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1750153558) (.leaf 1706855495)) (.branch 40 (.leaf 1664863537) (.leaf 1624127902))) (.branch 43 (.branch 42 (.leaf 1584601132) (.leaf 1546237959)) (.branch 44 (.leaf 1508995193) (.leaf 1472831612))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1437707853) (.branch 47 (.leaf 1403586320) (.leaf 1370431086))) (.branch 50 (.branch 49 (.leaf 1338207815) (.leaf 1306883670)) (.branch 51 (.leaf 1276427246) (.leaf 1246808490)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1217998638) (.leaf 1189970145)) (.branch 55 (.leaf 1162696632) (.leaf 1136152819))) (.branch 58 (.branch 57 (.leaf 1110314481) (.leaf 1085158386)) (.branch 59 (.leaf 1060662257) (.leaf 1036804718))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1013565254) (.branch 62 (.leaf 990924171) (.leaf 968862556))) (.branch 65 (.branch 64 (.leaf 947362240) (.leaf 926405762)) (.branch 66 (.leaf 905976340) (.leaf 886057835)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 866634725) (.leaf 847692075)) (.branch 70 (.leaf 829215511) (.leaf 811191195))) (.branch 73 (.branch 72 (.leaf 793605799) (.leaf 776446487)) (.branch 74 (.leaf 759700888) (.leaf 743357077))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 727403560) (.branch 77 (.leaf 711829247) (.leaf 696623442))) (.branch 80 (.branch 79 (.leaf 681775824) (.leaf 667276428)) (.branch 81 (.leaf 653115634) (.leaf 639284151)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 625773002) (.leaf 612573513)) (.branch 85 (.leaf 599677300) (.leaf 587076257))) (.branch 88 (.branch 87 (.leaf 574762542) (.leaf 562728572)) (.branch 89 (.leaf 550967009) (.leaf 539470749)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 528232917) (.branch 92 (.leaf 517246854) (.leaf 506506110))) (.branch 95 (.branch 94 (.leaf 496004436) (.leaf 485735779)) (.branch 96 (.leaf 475694269) (.leaf 465874214)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 456270099) (.leaf 446876569)) (.branch 100 (.leaf 437688433) (.leaf 428700651))) (.branch 103 (.branch 102 (.leaf 419908334) (.leaf 411306731)) (.branch 104 (.leaf 402891234) (.leaf 394657365))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 386600773) (.leaf 378717233)) (.branch 108 (.leaf 371002637) (.leaf 363452993))) (.branch 111 (.branch 110 (.leaf 356064420) (.leaf 348833145)) (.branch 112 (.leaf 341755496) (.leaf 334827904)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 328046896) (.leaf 321409092)) (.branch 116 (.leaf 314911203) (.leaf 308550026))) (.branch 119 (.branch 118 (.leaf 302322445) (.leaf 296225425)) (.branch 120 (.leaf 290256009) (.leaf 284411318)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 671).q*(generalMeanRows 671).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 671).q*(generalMeanRows 671).cutoff/2-2 = (1990/979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable227.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5147720081) (.branch 2 (.leaf 4978125420) (.leaf 4815992663))) (.branch 5 (.branch 4 (.leaf 4660899202) (.leaf 4512452198)) (.branch 6 (.leaf 4370285986) (.leaf 4234059757)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4103455478) (.leaf 3978176035)) (.branch 10 (.leaf 3857943555) (.leaf 3742497893))) (.branch 13 (.branch 12 (.leaf 3631595272) (.leaf 3525007037)) (.branch 14 (.leaf 3422518533) (.leaf 3323928080))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3229046041) (.branch 17 (.leaf 3137693962) (.leaf 3049703798))) (.branch 20 (.branch 19 (.leaf 2964917190) (.leaf 2883184811)) (.branch 21 (.leaf 2804365760) (.leaf 2728327002)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2654942855) (.leaf 2584094518)) (.branch 25 (.leaf 2515669626) (.leaf 2449561849))) (.branch 28 (.branch 27 (.leaf 2385670513) (.leaf 2323900247)) (.branch 29 (.leaf 2264160667) (.leaf 2206366064)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2150435131) (.branch 32 (.leaf 2096290698) (.leaf 2043859489))) (.branch 35 (.branch 34 (.leaf 1993071893) (.leaf 1943861755)) (.branch 36 (.leaf 1896166176) (.leaf 1849925327)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1805082276) (.leaf 1761582826)) (.branch 40 (.leaf 1719375362) (.leaf 1678410712))) (.branch 43 (.branch 42 (.leaf 1638642006) (.leaf 1600024560)) (.branch 44 (.leaf 1562515750) (.leaf 1526074904))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1490663203) (.branch 47 (.leaf 1456243574) (.leaf 1422780605))) (.branch 50 (.branch 49 (.leaf 1390240458) (.leaf 1358590783)) (.branch 51 (.leaf 1327800645) (.leaf 1297840453)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1268681886) (.leaf 1240297834)) (.branch 55 (.leaf 1212662335) (.leaf 1185750520))) (.branch 58 (.branch 57 (.leaf 1159538554) (.leaf 1134003590)) (.branch 59 (.leaf 1109123720) (.leaf 1084877925))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1061246037) (.branch 62 (.leaf 1038208697) (.leaf 1015747314))) (.branch 65 (.branch 64 (.leaf 993844030) (.leaf 972481689)) (.branch 66 (.leaf 951643795) (.leaf 931314493)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 911478529) (.leaf 892121229)) (.branch 70 (.leaf 873228470) (.leaf 854786653))) (.branch 73 (.branch 72 (.leaf 836782685) (.leaf 819203951)) (.branch 74 (.leaf 802038294) (.leaf 785273998))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 768899762) (.branch 77 (.leaf 752904689) (.leaf 737278264))) (.branch 80 (.branch 79 (.leaf 722010339) (.leaf 707091118)) (.branch 81 (.leaf 692511140) (.leaf 678261267)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 664332667) (.leaf 650716808)) (.branch 85 (.leaf 637405437) (.leaf 624390575))) (.branch 88 (.branch 87 (.leaf 611664505) (.leaf 599219757)) (.branch 89 (.leaf 587049102) (.leaf 575145543)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 563502304) (.branch 92 (.leaf 552112819) (.leaf 540970729))) (.branch 95 (.branch 94 (.leaf 530069871) (.leaf 519404269)) (.branch 96 (.leaf 508968131) (.leaf 498755839)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 488761941) (.leaf 478981150)) (.branch 100 (.leaf 469408332) (.leaf 460038505))) (.branch 103 (.branch 102 (.leaf 450866830) (.leaf 441888610)) (.branch 104 (.leaf 433099279) (.leaf 424494402))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 416069670) (.leaf 407820893)) (.branch 108 (.leaf 399743998) (.leaf 391835024))) (.branch 111 (.branch 110 (.leaf 384090117) (.leaf 376505532)) (.branch 112 (.leaf 369077621) (.leaf 361802835)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 354677720) (.leaf 347698913)) (.branch 116 (.leaf 340863140) (.leaf 334167211))) (.branch 119 (.branch 118 (.leaf 327608022) (.leaf 321182544)) (.branch 120 (.leaf 314887831) (.leaf 308721008)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 672).q*(generalMeanRows 672).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 672).q*(generalMeanRows 672).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5015616505) (.branch 2 (.leaf 4845657851) (.leaf 4683232587))) (.branch 5 (.branch 4 (.leaf 4527914710) (.leaf 4379308173)) (.branch 6 (.leaf 4237044270) (.leaf 4100779304)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3970192500) (.leaf 3844984135)) (.branch 10 (.leaf 3724873850) (.leaf 3609599133))) (.branch 13 (.branch 12 (.leaf 3498913942) (.leaf 3392587463)) (.branch 14 (.leaf 3290402974) (.leaf 3192156818))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3097657464) (.branch 17 (.leaf 3006724644) (.leaf 2919188571))) (.branch 20 (.branch 19 (.leaf 2834889218) (.leaf 2753675656)) (.branch 21 (.leaf 2675405441) (.leaf 2599944060)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2527164411) (.leaf 2456946322)) (.branch 25 (.leaf 2389176114) (.leaf 2323746191))) (.branch 28 (.branch 27 (.leaf 2260554659) (.leaf 2199504977)) (.branch 29 (.leaf 2140505626) (.leaf 2083469813)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2028315181) (.branch 32 (.leaf 1974963549) (.leaf 1923340668))) (.branch 35 (.branch 34 (.leaf 1873375991) (.leaf 1825002457)) (.branch 36 (.leaf 1778156297) (.leaf 1732776841)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1688806348) (.leaf 1646189841)) (.branch 40 (.leaf 1604874954) (.leaf 1564811788))) (.branch 43 (.branch 42 (.leaf 1525952778) (.leaf 1488252564)) (.branch 44 (.leaf 1451667875) (.leaf 1416157414))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1381681758) (.branch 47 (.leaf 1348203256) (.leaf 1315685938))) (.branch 50 (.branch 49 (.leaf 1284095427) (.leaf 1253398855)) (.branch 51 (.leaf 1223564789) (.leaf 1194563158)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1166365179) (.leaf 1138943299)) (.branch 55 (.leaf 1112271129) (.leaf 1086323387))) (.branch 58 (.branch 57 (.leaf 1061075845) (.leaf 1036505277)) (.branch 59 (.leaf 1012589410) (.leaf 989306875))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 966637168) (.branch 62 (.leaf 944560608) (.leaf 923058295))) (.branch 65 (.branch 64 (.leaf 902112075) (.leaf 881704505)) (.branch 66 (.leaf 861818821) (.leaf 842438904)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 823549253) (.leaf 805134955)) (.branch 70 (.leaf 787181657) (.leaf 769675545))) (.branch 73 (.branch 72 (.leaf 752603317) (.leaf 735952159)) (.branch 74 (.leaf 719709727) (.leaf 703864121))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 688403873) (.branch 77 (.leaf 673317920) (.leaf 658595594))) (.branch 80 (.branch 79 (.leaf 644226599) (.leaf 630201000)) (.branch 81 (.leaf 616509203) (.leaf 603141945)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 590090279) (.leaf 577345559)) (.branch 85 (.leaf 564899428) (.leaf 552743810))) (.branch 88 (.branch 87 (.leaf 540870892) (.leaf 529273121)) (.branch 89 (.leaf 517943185) (.leaf 506874013)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 496058757) (.branch 92 (.leaf 485490787) (.leaf 475163685))) (.branch 95 (.branch 94 (.leaf 465071230) (.leaf 455207398)) (.branch 96 (.leaf 445566348) (.leaf 436142422)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 426930129) (.leaf 417924149)) (.branch 100 (.leaf 409119318) (.leaf 400510626))) (.branch 103 (.branch 102 (.leaf 392093214) (.leaf 383862363)) (.branch 104 (.leaf 375813493) (.leaf 367942156))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360244033) (.leaf 352714927)) (.branch 108 (.leaf 345350760) (.leaf 338147573))) (.branch 111 (.branch 110 (.leaf 331101512) (.leaf 324208835)) (.branch 112 (.leaf 317465902) (.leaf 310869173)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 304415205) (.leaf 298100648)) (.branch 116 (.leaf 291922243) (.leaf 285876819))) (.branch 119 (.branch 118 (.leaf 279961289) (.leaf 274172648)) (.branch 120 (.leaf 268507970) (.leaf 262964406)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 673).q*(generalMeanRows 673).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 673).q*(generalMeanRows 673).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5054639484) (.branch 2 (.leaf 4883486903) (.leaf 4719892108))) (.branch 5 (.branch 4 (.leaf 4563429592) (.leaf 4413703699)) (.branch 6 (.leaf 4270346013) (.leaf 4133013037)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4001384116) (.leaf 3875159566)) (.branch 10 (.leaf 3754059004) (.leaf 3637819830))) (.branch 13 (.branch 12 (.leaf 3526195859) (.leaf 3418956084)) (.branch 14 (.leaf 3315883545) (.leaf 3216774309))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3121436531) (.branch 17 (.leaf 3029689601) (.leaf 2941363361))) (.branch 20 (.branch 19 (.leaf 2856297390) (.leaf 2774340345)) (.branch 21 (.leaf 2695349352) (.leaf 2619189451)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2545733083) (.leaf 2474859608)) (.branch 25 (.leaf 2406454875) (.leaf 2340410806))) (.branch 28 (.branch 27 (.leaf 2276625024) (.leaf 2215000501)) (.branch 29 (.leaf 2155445233) (.leaf 2097871940)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2042197780) (.branch 32 (.leaf 1988344093) (.leaf 1936236150))) (.branch 35 (.branch 34 (.leaf 1885802931) (.leaf 1836976908)) (.branch 36 (.leaf 1789693848) (.leaf 1743892627)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1699515056) (.leaf 1656505717)) (.branch 40 (.leaf 1614811809) (.leaf 1574383011))) (.branch 43 (.branch 42 (.leaf 1535171338) (.leaf 1497131025)) (.branch 44 (.leaf 1460218399) (.leaf 1424391776))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1389611350) (.branch 47 (.leaf 1355839100) (.leaf 1323038691))) (.branch 50 (.branch 49 (.leaf 1291175392) (.leaf 1260215992)) (.branch 51 (.leaf 1230128723) (.leaf 1200883186)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1172450282) (.leaf 1144802149)) (.branch 55 (.leaf 1117912098) (.leaf 1091754556))) (.branch 58 (.branch 57 (.leaf 1066305014) (.leaf 1041539970)) (.branch 59 (.leaf 1017436886) (.leaf 993974135))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 971130965) (.branch 62 (.leaf 948887451) (.leaf 927224460))) (.branch 65 (.branch 64 (.leaf 906123611) (.leaf 885567242)) (.branch 66 (.leaf 865538376) (.leaf 846020689)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 826998482) (.leaf 808456648)) (.branch 70 (.leaf 790380652) (.leaf 772756500))) (.branch 73 (.branch 72 (.leaf 755570715) (.leaf 738810317)) (.branch 74 (.leaf 722462801) (.leaf 706516112))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 690958630) (.branch 77 (.leaf 675779149) (.leaf 660966859))) (.branch 80 (.branch 79 (.leaf 646511331) (.leaf 632402499)) (.branch 81 (.leaf 618630644) (.leaf 605186383)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 592060651) (.leaf 579244690)) (.branch 85 (.leaf 566730036) (.leaf 554508508))) (.branch 88 (.branch 87 (.leaf 542572193) (.leaf 530913440)) (.branch 89 (.leaf 519524847) (.leaf 508399251)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 497529718) (.branch 92 (.leaf 486909537) (.leaf 476532206))) (.branch 95 (.branch 94 (.leaf 466391432) (.leaf 456481114)) (.branch 96 (.leaf 446795342) (.leaf 437328386)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 428074693) (.leaf 419028877)) (.branch 100 (.leaf 410185715) (.leaf 401540138))) (.branch 103 (.branch 102 (.leaf 393087230) (.leaf 384822218)) (.branch 104 (.leaf 376740470) (.leaf 368837489))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 361108906) (.leaf 353550479)) (.branch 108 (.leaf 346158087) (.leaf 338927724))) (.branch 111 (.branch 110 (.leaf 331855500) (.leaf 324937631)) (.branch 112 (.leaf 318170439) (.leaf 311550347)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305073879) (.leaf 298737651)) (.branch 116 (.leaf 292538370) (.leaf 286472836))) (.branch 119 (.branch 118 (.leaf 280537931) (.leaf 274730622)) (.branch 120 (.leaf 269047956) (.leaf 263487056)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 674).q*(generalMeanRows 674).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 674).q*(generalMeanRows 674).cutoff/2-2 = (1990/979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable227.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4928059400) (.branch 2 (.leaf 4756652868) (.leaf 4592875323))) (.branch 5 (.branch 4 (.leaf 4436297679) (.leaf 4286520894)) (.branch 6 (.leaf 4143173348) (.leaf 4005908509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3874402837) (.leaf 3748353914)) (.branch 10 (.leaf 3627478751) (.leaf 3511512268))) (.branch 13 (.branch 12 (.leaf 3400205918) (.leaf 3293326438)) (.branch 14 (.leaf 3190654719) (.leaf 3091984770))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2997122783) (.branch 17 (.leaf 2905886267) (.leaf 2818103267))) (.branch 20 (.branch 19 (.leaf 2733611638) (.leaf 2652258386)) (.branch 21 (.leaf 2573899056) (.leaf 2498397172)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2425623718) (.leaf 2355456660)) (.branch 25 (.leaf 2287780505) (.leaf 2222485889))) (.branch 28 (.branch 27 (.leaf 2159469200) (.leaf 2098632224)) (.branch 29 (.leaf 2039881817) (.leaf 1983129603)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1928291689) (.branch 32 (.leaf 1875288402) (.leaf 1824044043))) (.branch 35 (.branch 34 (.leaf 1774486656) (.leaf 1726547816)) (.branch 36 (.leaf 1680162428) (.leaf 1635268539)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1591807160) (.leaf 1549722110)) (.branch 40 (.leaf 1508959851) (.leaf 1469469353))) (.branch 43 (.branch 42 (.leaf 1431201955) (.leaf 1394111235)) (.branch 44 (.leaf 1358152895) (.leaf 1323284649))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1289466113) (.branch 47 (.leaf 1256658708) (.leaf 1224825569))) (.branch 50 (.branch 49 (.leaf 1193931453) (.leaf 1163942659)) (.branch 51 (.leaf 1134826948) (.leaf 1106553469)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1079092691) (.leaf 1052416339)) (.branch 55 (.leaf 1026497325) (.leaf 1001309700))) (.branch 58 (.branch 57 (.leaf 976828587) (.leaf 953030140)) (.branch 59 (.leaf 929891485) (.leaf 907390680))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 885506668) (.branch 62 (.leaf 864219234) (.leaf 843508968))) (.branch 65 (.branch 64 (.leaf 823357227) (.leaf 803746096)) (.branch 66 (.leaf 784658359) (.leaf 766077465)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 747987498) (.leaf 730373145)) (.branch 70 (.leaf 713219675) (.leaf 696512910))) (.branch 73 (.branch 72 (.leaf 680239197) (.leaf 664385390)) (.branch 74 (.leaf 648938826) (.leaf 633887303))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 619219062) (.branch 77 (.leaf 604922763) (.leaf 590987476))) (.branch 80 (.branch 79 (.leaf 577402652) (.leaf 564158119)) (.branch 81 (.leaf 551244057) (.leaf 538650986)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 526369754) (.leaf 514391523)) (.branch 85 (.leaf 502707751) (.leaf 491310188))) (.branch 88 (.branch 87 (.leaf 480190859) (.leaf 469342053)) (.branch 89 (.leaf 458756316) (.leaf 448426435)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 438345436) (.branch 92 (.leaf 428506567) (.leaf 418903295))) (.branch 95 (.branch 94 (.leaf 409529296) (.leaf 400378444)) (.branch 96 (.leaf 391444809) (.leaf 382722644)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 374206381) (.leaf 365890626)) (.branch 100 (.leaf 357770149) (.leaf 349839879))) (.branch 103 (.branch 102 (.leaf 342094899) (.leaf 334530440)) (.branch 104 (.leaf 327141877) (.leaf 319924720))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 312874614) (.leaf 305987331)) (.branch 108 (.leaf 299258766) (.leaf 292684934))) (.branch 111 (.branch 110 (.leaf 286261964) (.leaf 279986098)) (.branch 112 (.leaf 273853682) (.leaf 267861168)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 262005109) (.leaf 256282151)) (.branch 116 (.leaf 250689038) (.leaf 245222601))) (.branch 119 (.branch 118 (.leaf 239879759) (.leaf 234657517)) (.branch 120 (.leaf 229552961) (.leaf 224563256)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 675).q*(generalMeanRows 675).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 675).q*(generalMeanRows 675).cutoff/2-2 = (1990/979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable227.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5275917600) (.branch 2 (.leaf 5107003492) (.leaf 4945421981))) (.branch 5 (.branch 4 (.leaf 4790759850) (.leaf 4642632954)) (.branch 6 (.leaf 4500683675) (.leaf 4364578660)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4234006792) (.leaf 4108677374)) (.branch 10 (.leaf 3988318490) (.leaf 3872675534))) (.branch 13 (.branch 12 (.leaf 3761509872) (.leaf 3654597636)) (.branch 14 (.leaf 3551728626) (.leaf 3452705308))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3357341904) (.branch 17 (.leaf 3265463563) (.leaf 3176905593))) (.branch 20 (.branch 19 (.leaf 3091512763) (.leaf 3009138667)) (.branch 21 (.leaf 2929645125) (.leaf 2852901647)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2778784926) (.leaf 2707178379)) (.branch 25 (.leaf 2637971717) (.leaf 2571060546))) (.branch 28 (.branch 27 (.leaf 2506346005) (.leaf 2443734421)) (.branch 29 (.leaf 2383136993) (.leaf 2324469499)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2267652021) (.branch 32 (.leaf 2212608691) (.leaf 2159267451))) (.branch 35 (.branch 34 (.leaf 2107559833) (.leaf 2057420752)) (.branch 36 (.leaf 2008788312) (.leaf 1961603622)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1915810635) (.leaf 1871355978)) (.branch 40 (.leaf 1828188814) (.leaf 1786260697))) (.branch 43 (.branch 42 (.leaf 1745525441) (.leaf 1705939000)) (.branch 44 (.leaf 1667459354) (.leaf 1630046395))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1593661834) (.branch 47 (.leaf 1558269095) (.leaf 1523833234))) (.branch 50 (.branch 49 (.leaf 1490320852) (.leaf 1457700010)) (.branch 51 (.leaf 1425940162) (.leaf 1395012077)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1364887779) (.leaf 1335540477)) (.branch 55 (.leaf 1306944510) (.leaf 1279075290))) (.branch 58 (.branch 57 (.leaf 1251909251) (.leaf 1225423792)) (.branch 59 (.leaf 1199597238) (.leaf 1174408792))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1149838489) (.branch 62 (.leaf 1125867164) (.leaf 1102476406))) (.branch 65 (.branch 64 (.leaf 1079648527) (.leaf 1057366526)) (.branch 66 (.leaf 1035614060) (.leaf 1014375409)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 993635450) (.leaf 973379628)) (.branch 70 (.leaf 953593933) (.leaf 934264873))) (.branch 73 (.branch 72 (.leaf 915379449) (.leaf 896925139)) (.branch 74 (.leaf 878889869) (.leaf 861262000))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 844030305) (.branch 77 (.leaf 827183951) (.leaf 810712484))) (.branch 80 (.branch 79 (.leaf 794605813) (.leaf 778854192)) (.branch 81 (.leaf 763448207) (.leaf 748378759)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 733637059) (.leaf 719214604)) (.branch 85 (.leaf 705103174) (.leaf 691294816))) (.branch 88 (.branch 87 (.leaf 677781834) (.leaf 664556780)) (.branch 89 (.leaf 651612441) (.leaf 638941834)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 626538192) (.branch 92 (.leaf 614394960) (.leaf 602505783))) (.branch 95 (.branch 94 (.leaf 590864500) (.leaf 579465138)) (.branch 96 (.leaf 568301902) (.leaf 557369169)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 546661484) (.leaf 536173551)) (.branch 100 (.leaf 525900226) (.leaf 515836515))) (.branch 103 (.branch 102 (.leaf 505977568) (.leaf 496318671)) (.branch 104 (.leaf 486855242) (.leaf 477582830))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 468497104) (.leaf 459593854)) (.branch 108 (.leaf 450868985) (.leaf 442318513))) (.branch 111 (.branch 110 (.leaf 433938561) (.leaf 425725355)) (.branch 112 (.leaf 417675222) (.leaf 409784586)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 402049962) (.leaf 394467959)) (.branch 116 (.leaf 387035272) (.leaf 379748679))) (.branch 119 (.branch 118 (.leaf 372605043) (.leaf 365601304)) (.branch 120 (.leaf 358734479) (.leaf 352001660)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 676).q*(generalMeanRows 676).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 676).q*(generalMeanRows 676).cutoff/2-2 = (3932/1935:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable229.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5012290221) (.branch 2 (.leaf 4842507771) (.leaf 4680203237))) (.branch 5 (.branch 4 (.leaf 4524956605) (.leaf 4376377297)) (.branch 6 (.leaf 4234101599) (.leaf 4097790374)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3967127009) (.leaf 3841815576)) (.branch 10 (.leaf 3721579177) (.leaf 3606158456))) (.branch 13 (.branch 12 (.leaf 3495310242) (.leaf 3388806334)) (.branch 14 (.leaf 3286432388) (.leaf 3187986903))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3093280304) (.branch 17 (.leaf 3002134094) (.leaf 2914380089))) (.branch 20 (.branch 19 (.leaf 2829859709) (.leaf 2748423324)) (.branch 21 (.leaf 2669929665) (.leaf 2594245268)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2521243968) (.leaf 2450806431)) (.branch 25 (.leaf 2382819723) (.leaf 2317176904))) (.branch 28 (.branch 27 (.leaf 2253776658) (.leaf 2192522951)) (.branch 29 (.leaf 2133324707) (.leaf 2076095511)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2020753330) (.branch 32 (.leaf 1967220260) (.leaf 1915422280))) (.branch 35 (.branch 34 (.leaf 1865289028) (.leaf 1816753592)) (.branch 36 (.leaf 1769752317) (.leaf 1724224615)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1680112799) (.leaf 1637361920)) (.branch 40 (.leaf 1595919615) (.leaf 1555735971))) (.branch 43 (.branch 42 (.leaf 1516763386) (.leaf 1478956448)) (.branch 44 (.leaf 1442271818) (.leaf 1406668121))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1372105840) (.branch 47 (.leaf 1338547222) (.leaf 1305956184))) (.branch 50 (.branch 49 (.leaf 1274298229) (.leaf 1243540364)) (.branch 51 (.leaf 1213651023) (.leaf 1184599996)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1156358359) (.leaf 1128898414)) (.branch 55 (.leaf 1102193625) (.leaf 1076218560))) (.branch 58 (.branch 57 (.leaf 1050948840) (.leaf 1026361087)) (.branch 59 (.leaf 1002432874) (.leaf 979142682))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 956469855) (.branch 62 (.leaf 934394558) (.leaf 912897742))) (.branch 65 (.branch 64 (.leaf 891961104) (.leaf 871567055)) (.branch 66 (.leaf 851698683) (.leaf 832339727)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 813474544) (.leaf 795088080)) (.branch 70 (.leaf 777165849) (.leaf 759693900))) (.branch 73 (.branch 72 (.leaf 742658800) (.leaf 726047606)) (.branch 74 (.leaf 709847847) (.leaf 694047502))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 678634981) (.branch 77 (.leaf 663599105) (.leaf 648929090))) (.branch 80 (.branch 79 (.leaf 634614528) (.leaf 620645377)) (.branch 81 (.leaf 607011937) (.leaf 593704842)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 580715044) (.leaf 568033801)) (.branch 85 (.leaf 555652662) (.leaf 543563460))) (.branch 88 (.branch 87 (.leaf 531758293) (.leaf 520229522)) (.branch 89 (.leaf 508969754) (.leaf 497971835)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 487228841) (.branch 92 (.leaf 476734067) (.leaf 466481022))) (.branch 95 (.branch 94 (.leaf 456463415) (.leaf 446675154)) (.branch 96 (.leaf 437110334) (.leaf 427763233)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 418628301) (.leaf 409700157)) (.branch 100 (.leaf 400973583) (.leaf 392443515))) (.branch 103 (.branch 102 (.leaf 384105041) (.leaf 375953392)) (.branch 104 (.leaf 367983941) (.leaf 360192193))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 352573784) (.leaf 345124477)) (.branch 108 (.leaf 337840152) (.leaf 330716810))) (.branch 111 (.branch 110 (.leaf 323750563) (.leaf 316937630)) (.branch 112 (.leaf 310274337) (.leaf 303757113)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 297382483) (.leaf 291147068)) (.branch 116 (.leaf 285047579) (.leaf 279080820))) (.branch 119 (.branch 118 (.leaf 273243677) (.leaf 267533120)) (.branch 120 (.leaf 261946201) (.leaf 256480049)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 677).q*(generalMeanRows 677).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 677).q*(generalMeanRows 677).cutoff/2-2 = (3932/1935:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable229.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4969174948) (.branch 2 (.leaf 4798476542) (.leaf 4635373799))) (.branch 5 (.branch 4 (.leaf 4479437445) (.leaf 4330268362)) (.branch 6 (.leaf 4187494962) (.leaf 4050770834)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3919772649) (.leaf 3794198270)) (.branch 10 (.leaf 3673765061) (.leaf 3558208356))) (.branch 13 (.branch 12 (.leaf 3447280076) (.leaf 3340747474)) (.branch 14 (.leaf 3238391999) (.leaf 3140008256))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3045403061) (.branch 17 (.leaf 2954394579) (.leaf 2866811530))) (.branch 20 (.branch 19 (.leaf 2782492466) (.leaf 2701285103)) (.branch 21 (.leaf 2623045710) (.leaf 2547638544)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2474935327) (.leaf 2404814770)) (.branch 25 (.leaf 2337162123) (.leaf 2271868768))) (.branch 28 (.branch 27 (.leaf 2208831836) (.leaf 2147953849)) (.branch 29 (.leaf 2089142399) (.leaf 2032309837)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1977372987) (.branch 32 (.leaf 1924252888) (.leaf 1872874539))) (.branch 35 (.branch 34 (.leaf 1823166677) (.leaf 1775061553)) (.branch 36 (.leaf 1728494738) (.leaf 1683404932)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1639733788) (.leaf 1597425751)) (.branch 40 (.leaf 1556427897) (.leaf 1516689795))) (.branch 43 (.branch 42 (.leaf 1478163369) (.leaf 1440802767)) (.branch 44 (.leaf 1404564249) (.leaf 1369406069))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1335288370) (.branch 47 (.leaf 1302173088) (.leaf 1270023853))) (.branch 50 (.branch 49 (.leaf 1238805908) (.leaf 1208486021)) (.branch 51 (.leaf 1179032407) (.leaf 1150414658)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1122603671) (.leaf 1095571582)) (.branch 55 (.leaf 1069291707) (.leaf 1043738480))) (.branch 58 (.branch 57 (.leaf 1018887403) (.leaf 994714987)) (.branch 59 (.leaf 971198710) (.leaf 948316964))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 926049018) (.branch 62 (.leaf 904374970) (.leaf 883275711))) (.branch 65 (.branch 64 (.leaf 862732886) (.leaf 842728861)) (.branch 66 (.leaf 823246688) (.leaf 804270074)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 785783348) (.leaf 767771438)) (.branch 70 (.leaf 750219840) (.leaf 733114592))) (.branch 73 (.branch 72 (.leaf 716442254) (.leaf 700189879)) (.branch 74 (.leaf 684344996) (.leaf 668895587))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 653830066) (.branch 77 (.leaf 639137264) (.leaf 624806408))) (.branch 80 (.branch 79 (.leaf 610827104) (.leaf 597189322)) (.branch 81 (.leaf 583883383) (.leaf 570899937)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 558229959) (.leaf 545864726)) (.branch 85 (.leaf 533795812) (.leaf 522015073))) (.branch 88 (.branch 87 (.leaf 510514634) (.leaf 499286881)) (.branch 89 (.leaf 488324447) (.leaf 477620208)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 467167268) (.branch 92 (.leaf 456958951) (.leaf 446988794))) (.branch 95 (.branch 94 (.leaf 437250539) (.leaf 427738124)) (.branch 96 (.leaf 418445674) (.leaf 409367498)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 400498078) (.leaf 391832065)) (.branch 100 (.leaf 383364272) (.leaf 375089669))) (.branch 103 (.branch 102 (.leaf 367003374) (.leaf 359100652)) (.branch 104 (.leaf 351376907) (.leaf 343827677))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 336448630) (.leaf 329235561)) (.branch 108 (.leaf 322184384) (.leaf 315291129))) (.branch 111 (.branch 110 (.leaf 308551942) (.leaf 301963074)) (.branch 112 (.leaf 295520884) (.leaf 289221831)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 283062472) (.leaf 277039459)) (.branch 116 (.leaf 271149537) (.leaf 265389537))) (.branch 119 (.branch 118 (.leaf 259756379) (.leaf 254247064)) (.branch 120 (.leaf 248858673) (.leaf 243588366)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 678).q*(generalMeanRows 678).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 678).q*(generalMeanRows 678).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5031702171) (.branch 2 (.leaf 4861141037) (.leaf 4698154137))) (.branch 5 (.branch 4 (.leaf 4542312208) (.leaf 4393216209)) (.branch 6 (.leaf 4250494685) (.leaf 4113801413)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3982813296) (.leaf 3857228477)) (.branch 10 (.leaf 3736764634) (.leaf 3621157447))) (.branch 13 (.branch 12 (.leaf 3510159217) (.leaf 3403537599)) (.branch 14 (.leaf 3301074467) (.leaf 3202564870))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3107816086) (.branch 17 (.leaf 3016646753) (.leaf 2928886077))) (.branch 20 (.branch 19 (.leaf 2844373104) (.leaf 2762956050)) (.branch 21 (.leaf 2684491692) (.leaf 2608844793)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2535887589) (.leaf 2465499299)) (.branch 25 (.leaf 2397565685) (.leaf 2331978636))) (.branch 28 (.branch 27 (.leaf 2268635787) (.leaf 2207440162)) (.branch 29 (.leaf 2148299847) (.leaf 2091127682)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2035840975) (.branch 32 (.leaf 1982361241) (.leaf 1930613948))) (.branch 35 (.branch 34 (.leaf 1880528292) (.leaf 1832036977)) (.branch 36 (.leaf 1785076017) (.leaf 1739584547)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1695504644) (.leaf 1652781169)) (.branch 40 (.leaf 1611361603) (.leaf 1571195912))) (.branch 43 (.branch 42 (.leaf 1532236405) (.leaf 1494437608)) (.branch 44 (.leaf 1457756146) (.leaf 1422150630))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1387581548) (.branch 47 (.leaf 1354011174) (.leaf 1321403465))) (.branch 50 (.branch 49 (.leaf 1289723979) (.leaf 1258939792)) (.branch 51 (.leaf 1229019418) (.leaf 1199932735)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1171650919) (.leaf 1144146377)) (.branch 55 (.leaf 1117392683) (.leaf 1091364526))) (.branch 58 (.branch 57 (.leaf 1066037646) (.leaf 1041388792)) (.branch 59 (.leaf 1017395665) (.leaf 994036877))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 971291904) (.branch 62 (.leaf 949141045) (.leaf 927565385))) (.branch 65 (.branch 64 (.leaf 906546756) (.leaf 886067701)) (.branch 66 (.leaf 866111444) (.leaf 846661855)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 827703421) (.leaf 809221220)) (.branch 70 (.leaf 791200893) (.leaf 773628615))) (.branch 73 (.branch 72 (.leaf 756491077) (.leaf 739775457)) (.branch 74 (.leaf 723469405) (.leaf 707561015))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 692038812) (.branch 77 (.leaf 676891727) (.leaf 662109086))) (.branch 80 (.branch 79 (.leaf 647680588) (.leaf 633596291)) (.branch 81 (.leaf 619846597) (.leaf 606422238)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 593314260) (.leaf 580514011)) (.branch 85 (.leaf 568013131) (.leaf 555803536))) (.branch 88 (.branch 87 (.leaf 543877410) (.leaf 532227192)) (.branch 89 (.leaf 520845566) (.leaf 509725455)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 498860004) (.branch 92 (.leaf 488242579) (.leaf 477866754))) (.branch 95 (.branch 94 (.leaf 467726305) (.leaf 457815199)) (.branch 96 (.leaf 448127591) (.leaf 438657815)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 429400375) (.leaf 420349943)) (.branch 100 (.leaf 411501349) (.leaf 402849578))) (.branch 103 (.branch 102 (.leaf 394389763) (.leaf 386117178)) (.branch 104 (.leaf 378027237) (.leaf 370115485))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 362377594) (.leaf 354809363)) (.branch 108 (.leaf 347406707) (.leaf 340165657))) (.branch 111 (.branch 110 (.leaf 333082355) (.leaf 326153051)) (.branch 112 (.leaf 319374096) (.leaf 312741944)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 306253145) (.leaf 299904342)) (.branch 116 (.leaf 293692269) (.leaf 287613746))) (.branch 119 (.branch 118 (.leaf 281665680) (.leaf 275845058)) (.branch 120 (.leaf 270148949) (.leaf 264574494)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 679).q*(generalMeanRows 679).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 679).q*(generalMeanRows 679).cutoff/2-2 = (8026/3883:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable230.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4967020012) (.branch 2 (.leaf 4796330705) (.leaf 4633250859))) (.branch 5 (.branch 4 (.leaf 4477349471) (.leaf 4328225853)) (.branch 6 (.leaf 4185506993) (.leaf 4048845189)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3917915942) (.leaf 3792416058)) (.branch 10 (.leaf 3672061946) (.leaf 3556588076))) (.branch 13 (.branch 12 (.leaf 3445745594) (.leaf 3339301052)) (.branch 14 (.leaf 3237035272) (.leaf 3138742298))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3044228442) (.branch 17 (.leaf 2953311422) (.leaf 2865819560))) (.branch 20 (.branch 19 (.leaf 2781591056) (.leaf 2700473316)) (.branch 21 (.leaf 2622322335) (.leaf 2547002132)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2474384224) (.leaf 2404347142)) (.branch 25 (.leaf 2336775985) (.leaf 2271562008))) (.branch 28 (.branch 27 (.leaf 2208602233) (.leaf 2147799098)) (.branch 29 (.leaf 2089060123) (.leaf 2032297605)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1977428330) (.branch 32 (.leaf 1924373310) (.leaf 1873057530))) (.branch 35 (.branch 34 (.leaf 1823409720) (.leaf 1775362138)) (.branch 36 (.leaf 1728850368) (.leaf 1683813128)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1640192101) (.leaf 1597931761)) (.branch 40 (.leaf 1556979223) (.leaf 1517284098))) (.branch 43 (.branch 42 (.leaf 1478798353) (.leaf 1441476188)) (.branch 44 (.leaf 1405273912) (.leaf 1370149832))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1336064148) (.branch 47 (.leaf 1302978850) (.leaf 1270857630))) (.branch 50 (.branch 49 (.leaf 1239665785) (.leaf 1209370144)) (.branch 51 (.leaf 1179938983) (.leaf 1151341951)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1123550006) (.leaf 1096535344)) (.branch 55 (.leaf 1070271337) (.leaf 1044732480))) (.branch 58 (.branch 57 (.leaf 1019894329) (.leaf 995733455)) (.branch 59 (.leaf 972227390) (.leaf 949354581))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 927094351) (.branch 62 (.leaf 905426850) (.leaf 884333020))) (.branch 65 (.branch 64 (.leaf 863794557) (.leaf 843793876)) (.branch 66 (.leaf 824314077) (.leaf 805338911)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 786852755) (.leaf 768840580)) (.branch 70 (.leaf 751287923) (.leaf 734180866))) (.branch 73 (.branch 72 (.leaf 717506006) (.leaf 701250436)) (.branch 74 (.leaf 685401722) (.leaf 669947882))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 654877365) (.branch 77 (.leaf 640179036) (.leaf 625842152))) (.branch 80 (.branch 79 (.leaf 611856353) (.leaf 598211639)) (.branch 81 (.leaf 584898357) (.leaf 571907187)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 559229129) (.leaf 546855488)) (.branch 85 (.leaf 534777860) (.leaf 522988125))) (.branch 88 (.branch 87 (.leaf 511478432) (.leaf 500241186)) (.branch 89 (.leaf 489269043) (.leaf 478554897)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 468091870) (.branch 92 (.leaf 457873307) (.leaf 447892760))) (.branch 95 (.branch 94 (.leaf 438143987) (.leaf 428620942)) (.branch 96 (.leaf 419317766) (.leaf 410228780)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 401348481) (.leaf 392671532)) (.branch 100 (.leaf 384192758) (.leaf 375907139))) (.branch 103 (.branch 102 (.leaf 367809807) (.leaf 359896035)) (.branch 104 (.leaf 352161237) (.leaf 344600960))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337210881) (.leaf 329986803)) (.branch 108 (.leaf 322924647) (.leaf 316020453))) (.branch 111 (.branch 110 (.leaf 309270370) (.leaf 302670657)) (.branch 112 (.leaf 296217679) (.leaf 289907901)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 283737884) (.leaf 277704286)) (.branch 116 (.leaf 271803855) (.leaf 266033428))) (.branch 119 (.branch 118 (.leaf 260389928) (.leaf 254870359)) (.branch 120 (.leaf 249471806) (.leaf 244191432)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 680).q*(generalMeanRows 680).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 680).q*(generalMeanRows 680).cutoff/2-2 = (8026/3883:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable230.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4986921308) (.branch 2 (.leaf 4815613289) (.leaf 4651928059))) (.branch 5 (.branch 4 (.leaf 4495434810) (.leaf 4345733002)) (.branch 6 (.leaf 4202449716) (.leaf 4065237308)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3933771290) (.leaf 3807748448)) (.branch 10 (.leaf 3686885137) (.leaf 3570915746))) (.branch 13 (.branch 12 (.leaf 3459591309) (.leaf 3352678249)) (.branch 14 (.leaf 3249957233) (.leaf 3151222133))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3056279076) (.branch 17 (.leaf 2964945576) (.leaf 2877049742))) (.branch 20 (.branch 19 (.leaf 2792429550) (.leaf 2710932173)) (.branch 21 (.leaf 2632413365) (.leaf 2556736897)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2483774036) (.leaf 2413403058)) (.branch 25 (.leaf 2345508804) (.leaf 2279982268))) (.branch 28 (.branch 27 (.leaf 2216720212) (.leaf 2155624813)) (.branch 29 (.leaf 2096603331) (.leaf 2039567802)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1984434757) (.branch 32 (.leaf 1931124951) (.leaf 1879563116))) (.branch 35 (.branch 34 (.leaf 1829677732) (.leaf 1781400811)) (.branch 36 (.leaf 1734667692) (.leaf 1689416857)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1645589752) (.leaf 1603130620)) (.branch 40 (.leaf 1561986351) (.leaf 1522106333))) (.branch 43 (.branch 42 (.leaf 1483442317) (.leaf 1445948290)) (.branch 44 (.leaf 1409580354) (.leaf 1374296614))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1340057071) (.branch 47 (.leaf 1306823524) (.leaf 1274559475))) (.branch 50 (.branch 49 (.leaf 1243230042) (.leaf 1212801874)) (.branch 51 (.leaf 1183243072) (.leaf 1154523121)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1126612813) (.leaf 1099484185)) (.branch 55 (.leaf 1073110456) (.leaf 1047465972))) (.branch 58 (.branch 57 (.leaf 1022526144) (.leaf 998267402)) (.branch 59 (.leaf 974667141) (.leaf 951703678))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 929356207) (.branch 62 (.leaf 907604754) (.leaf 886430143))) (.branch 65 (.branch 64 (.leaf 865813954) (.leaf 845738489)) (.branch 66 (.leaf 826186740) (.leaf 807142355)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 788589608) (.leaf 770513372)) (.branch 70 (.leaf 752899092) (.leaf 735732756))) (.branch 73 (.branch 72 (.leaf 719000876) (.leaf 702690460)) (.branch 74 (.leaf 686788990) (.leaf 671284406))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 656165082) (.branch 77 (.leaf 641419808) (.leaf 627037772))) (.branch 80 (.branch 79 (.leaf 613008544) (.leaf 599322058)) (.branch 81 (.leaf 585968599) (.leaf 572938786)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 560223559) (.leaf 547814167)) (.branch 85 (.leaf 535702151) (.leaf 523879340))) (.branch 88 (.branch 87 (.leaf 512337829) (.leaf 501069978)) (.branch 89 (.leaf 490068395) (.leaf 479325928)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 468835657) (.branch 92 (.leaf 458590883) (.leaf 448585120))) (.branch 95 (.branch 94 (.leaf 438812087) (.leaf 429265700)) (.branch 96 (.leaf 419940064) (.leaf 410829467)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 401928372) (.leaf 393231410)) (.branch 100 (.leaf 384733377) (.leaf 376429223))) (.branch 103 (.branch 102 (.leaf 368314049) (.leaf 360383105)) (.branch 104 (.leaf 352631775) (.leaf 345055585))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337650186) (.leaf 330411356)) (.branch 108 (.leaf 323334997) (.leaf 316417125))) (.branch 111 (.branch 110 (.leaf 309653870) (.leaf 303041472)) (.branch 112 (.leaf 296576275) (.leaf 290254726)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284073370) (.leaf 278028847)) (.branch 116 (.leaf 272117890) (.leaf 266337320))) (.branch 119 (.branch 118 (.leaf 260684044) (.leaf 255155053)) (.branch 120 (.leaf 249747419) (.leaf 244458290)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 681).q*(generalMeanRows 681).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 681).q*(generalMeanRows 681).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4923596001) (.branch 2 (.leaf 4752186446) (.leaf 4588434801))) (.branch 5 (.branch 4 (.leaf 4431908473) (.leaf 4282205233)) (.branch 6 (.leaf 4138950567) (.leaf 4001795313)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3870413548) (.leaf 3744500691)) (.branch 10 (.leaf 3623771799) (.leaf 3507960024))) (.branch 13 (.branch 12 (.leaf 3396815221) (.leaf 3290102689)) (.branch 14 (.leaf 3187602023) (.leaf 3089106068))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2994419974) (.branch 17 (.leaf 2903360316) (.leaf 2815754309))) (.branch 20 (.branch 19 (.leaf 2731439067) (.leaf 2650260943)) (.branch 21 (.leaf 2572074902) (.leaf 2496743962)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2424138663) (.leaf 2354136587)) (.branch 25 (.leaf 2286621909) (.leaf 2221484982))) (.branch 28 (.branch 27 (.leaf 2158621954) (.leaf 2097934412)) (.branch 29 (.leaf 2039329051) (.leaf 1982717362)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1928015354) (.branch 32 (.leaf 1875143279) (.leaf 1824025389))) (.branch 35 (.branch 34 (.leaf 1774589699) (.leaf 1726767777)) (.branch 36 (.leaf 1680494535) (.leaf 1635708044)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1592349355) (.leaf 1550362334)) (.branch 40 (.leaf 1509693506) (.leaf 1470291910))) (.branch 43 (.branch 42 (.leaf 1432108961) (.leaf 1395098324)) (.branch 44 (.leaf 1359215793) (.leaf 1324419176))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1290668189) (.branch 47 (.leaf 1257924358) (.leaf 1226150924))) (.branch 50 (.branch 49 (.leaf 1195312753) (.leaf 1165376254)) (.branch 51 (.leaf 1136309298) (.leaf 1108081148)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1080662385) (.leaf 1054024844)) (.branch 55 (.leaf 1028141551) (.leaf 1002986664))) (.branch 58 (.branch 57 (.leaf 978535420) (.leaf 954764078)) (.branch 59 (.leaf 931649873) (.leaf 909170967))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 887306407) (.branch 62 (.leaf 866036078) (.leaf 845340672))) (.branch 65 (.branch 64 (.leaf 825201640) (.leaf 805601164)) (.branch 66 (.leaf 786522121) (.leaf 767948049)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 749863120) (.leaf 732252107)) (.branch 70 (.leaf 715100362) (.leaf 698393787))) (.branch 73 (.branch 72 (.leaf 682118807) (.leaf 666262354)) (.branch 74 (.leaf 650811836) (.leaf 635755122))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 621080522) (.branch 77 (.leaf 606776763) (.leaf 592832976))) (.branch 80 (.branch 79 (.leaf 579238678) (.leaf 565983752)) (.branch 81 (.leaf 553058436) (.leaf 540453307)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 528159265) (.leaf 516167521)) (.branch 85 (.leaf 504469584) (.leaf 493057249))) (.branch 88 (.branch 87 (.leaf 481922587) (.leaf 471057929)) (.branch 89 (.leaf 460455862) (.leaf 450109214)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440011047) (.branch 92 (.leaf 430154646) (.leaf 420533512))) (.branch 95 (.branch 94 (.leaf 411141353) (.leaf 401972076)) (.branch 96 (.leaf 393019779) (.leaf 384278744)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375743432) (.leaf 367408471)) (.branch 100 (.leaf 359268658) (.leaf 351318944))) (.branch 103 (.branch 102 (.leaf 343554435) (.leaf 335970383)) (.branch 104 (.leaf 328562181) (.leaf 321325360))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314255581) (.leaf 307348633)) (.branch 108 (.leaf 300600427) (.leaf 294006993))) (.branch 111 (.branch 110 (.leaf 287564474) (.leaf 281269125)) (.branch 112 (.leaf 275117304) (.leaf 269105476)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263230202) (.leaf 257488142)) (.branch 116 (.leaf 251876046) (.leaf 246390755))) (.branch 119 (.branch 118 (.leaf 241029198) (.leaf 235788386)) (.branch 120 (.leaf 230665411) (.leaf 225657447)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 682).q*(generalMeanRows 682).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 682).q*(generalMeanRows 682).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5236997194) (.branch 2 (.leaf 5069212918) (.leaf 4908765844))) (.branch 5 (.branch 4 (.leaf 4755238816) (.leaf 4608244169)) (.branch 6 (.leaf 4467421154) (.leaf 4332433638)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4202968049) (.leaf 4078731528)) (.branch 10 (.leaf 3959450267) (.leaf 3844868013))) (.branch 13 (.branch 12 (.leaf 3734744711) (.leaf 3628855274)) (.branch 14 (.leaf 3526988469) (.leaf 3428945897))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3334541073) (.branch 17 (.leaf 3243598571) (.leaf 3155953253))) (.branch 20 (.branch 19 (.leaf 3071449558) (.leaf 2989940848)) (.branch 21 (.leaf 2911288808) (.leaf 2835362893)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2762039818) (.leaf 2691203085)) (.branch 25 (.leaf 2622742552) (.leaf 2556554026))) (.branch 28 (.branch 27 (.leaf 2492538891) (.leaf 2430603760)) (.branch 29 (.leaf 2370660157) (.leaf 2312624215)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2256416396) (.branch 32 (.leaf 2201961237) (.leaf 2149187105))) (.branch 35 (.branch 34 (.leaf 2098025973) (.leaf 2048413211)) (.branch 36 (.leaf 2000287388) (.leaf 1953590087)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1908265741) (.leaf 1864261461)) (.branch 40 (.leaf 1821526898) (.leaf 1780014092))) (.branch 43 (.branch 42 (.leaf 1739677345) (.leaf 1700473098)) (.branch 44 (.leaf 1662359811) (.leaf 1625297856))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1589249414) (.branch 47 (.leaf 1554178381) (.leaf 1520050272))) (.branch 50 (.branch 49 (.leaf 1486832141) (.leaf 1454492498)) (.branch 51 (.leaf 1423001232) (.leaf 1392329546)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1362449881) (.leaf 1333335860)) (.branch 55 (.leaf 1304962225) (.leaf 1277304781))) (.branch 58 (.branch 57 (.leaf 1250340345) (.leaf 1224046692)) (.branch 59 (.leaf 1198402510) (.leaf 1173387357))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1148981613) (.branch 62 (.leaf 1125166448) (.leaf 1101923777))) (.branch 65 (.branch 64 (.leaf 1079236228) (.leaf 1057087108)) (.branch 66 (.leaf 1035460369) (.leaf 1014340580)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 993712897) (.leaf 973563036)) (.branch 70 (.leaf 953877247) (.leaf 934642291))) (.branch 73 (.branch 72 (.leaf 915845415) (.leaf 897474330)) (.branch 74 (.leaf 879517192) (.leaf 861962581))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 844799482) (.branch 77 (.leaf 828017268) (.leaf 811605683))) (.branch 80 (.branch 79 (.leaf 795554824) (.leaf 779855128)) (.branch 81 (.leaf 764497359) (.leaf 749472590)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 734772191) (.leaf 720387820)) (.branch 85 (.leaf 706311407) (.leaf 692535144))) (.branch 88 (.branch 87 (.leaf 679051476) (.leaf 665853089)) (.branch 89 (.leaf 652932900) (.leaf 640284048)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 627899887) (.branch 92 (.leaf 615773974) (.leaf 603900066))) (.branch 95 (.branch 94 (.leaf 592272106) (.leaf 580884222)) (.branch 96 (.leaf 569730715) (.leaf 558806056)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 548104877) (.leaf 537621967)) (.branch 100 (.leaf 527352265) (.leaf 517290854))) (.branch 103 (.branch 102 (.leaf 507432958) (.leaf 497773934)) (.branch 104 (.leaf 488309270) (.leaf 479034577))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 469945589) (.leaf 461038154)) (.branch 108 (.leaf 452308235) (.leaf 443751902))) (.branch 111 (.branch 110 (.leaf 435365328) (.leaf 427144790)) (.branch 112 (.leaf 419086662) (.leaf 411187412)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 403443599) (.leaf 395851873)) (.branch 116 (.leaf 388408966) (.leaf 381111695))) (.branch 119 (.branch 118 (.leaf 373956956) (.leaf 366941725)) (.branch 120 (.leaf 360063050) (.leaf 353318053)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 683).q*(generalMeanRows 683).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 683).q*(generalMeanRows 683).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5100795176) (.branch 2 (.leaf 4932546186) (.leaf 4771706050))) (.branch 5 (.branch 4 (.leaf 4617854378) (.leaf 4470600442)) (.branch 6 (.leaf 4329580588) (.leaf 4194455926)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4064910256) (.leaf 3940648220)) (.branch 10 (.leaf 3821393625) (.leaf 3706887941))) (.branch 13 (.branch 12 (.leaf 3596888937) (.leaf 3491169444)) (.branch 14 (.leaf 3389516235) (.leaf 3291729001))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3197619424) (.branch 17 (.leaf 3107010318) (.leaf 3019734856))) (.branch 20 (.branch 19 (.leaf 2935635854) (.leaf 2854565113)) (.branch 21 (.leaf 2776382813) (.leaf 2700956966)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2628162892) (.leaf 2557882753)) (.branch 25 (.leaf 2490005114) (.leaf 2424424535))) (.branch 28 (.branch 27 (.leaf 2361041198) (.leaf 2299760557)) (.branch 29 (.leaf 2240493017) (.leaf 2183153630)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2127661818) (.branch 32 (.leaf 2073941111) (.leaf 2021918905))) (.branch 35 (.branch 34 (.leaf 1971526234) (.leaf 1922697563)) (.branch 36 (.leaf 1875370585) (.leaf 1829486041)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1784987542) (.leaf 1741821416)) (.branch 40 (.leaf 1699936549) (.leaf 1659284246))) (.branch 43 (.branch 42 (.leaf 1619818099) (.leaf 1581493861)) (.branch 44 (.leaf 1544269329) (.leaf 1508104235))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1472960143) (.branch 47 (.leaf 1438800348) (.leaf 1405589792))) (.branch 50 (.branch 49 (.leaf 1373294969) (.leaf 1341883852)) (.branch 51 (.leaf 1311325814) (.leaf 1281591553)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1252653030) (.leaf 1224483400)) (.branch 55 (.leaf 1197056957) (.leaf 1170349072))) (.branch 58 (.branch 57 (.leaf 1144336142) (.leaf 1118995541)) (.branch 59 (.leaf 1094305568) (.leaf 1070245406))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1046795077) (.branch 62 (.leaf 1023935402) (.leaf 1001647963))) (.branch 65 (.branch 64 (.leaf 979915065) (.leaf 958719707)) (.branch 66 (.leaf 938045544) (.leaf 917876858)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 898198530) (.leaf 878996014)) (.branch 70 (.leaf 860255305) (.leaf 841962921))) (.branch 73 (.branch 72 (.leaf 824105875) (.leaf 806671656)) (.branch 74 (.leaf 789648205) (.leaf 773023897))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 756787519) (.branch 77 (.leaf 740928258) (.leaf 725435677))) (.branch 80 (.branch 79 (.leaf 710299701) (.leaf 695510605)) (.branch 81 (.leaf 681058995) (.leaf 666935794)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 653132233) (.leaf 639639832)) (.branch 85 (.leaf 626450394) (.leaf 613555990))) (.branch 88 (.branch 87 (.leaf 600948947) (.leaf 588621842)) (.branch 89 (.leaf 576567489) (.leaf 564778929)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 553249423) (.branch 92 (.leaf 541972441) (.leaf 530941658))) (.branch 95 (.branch 94 (.leaf 520150940) (.leaf 509594343)) (.branch 96 (.leaf 499266102) (.leaf 489160622)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 479272480) (.leaf 469596409)) (.branch 100 (.leaf 460127298) (.leaf 450860185))) (.branch 103 (.branch 102 (.leaf 441790250) (.leaf 432912814)) (.branch 104 (.leaf 424223328) (.leaf 415717374))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 407390657) (.leaf 399239000)) (.branch 108 (.leaf 391258344) (.leaf 383444740))) (.branch 111 (.branch 110 (.leaf 375794348) (.leaf 368303431)) (.branch 112 (.leaf 360968353) (.leaf 353785574)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 346751649) (.leaf 339863225)) (.branch 116 (.leaf 333117034) (.leaf 326509896))) (.branch 119 (.branch 118 (.leaf 320038711) (.leaf 313700461)) (.branch 120 (.leaf 307492204) (.leaf 301411071)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 684).q*(generalMeanRows 684).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 684).q*(generalMeanRows 684).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4984610131) (.branch 2 (.leaf 4813316348) (.leaf 4649658974))) (.branch 5 (.branch 4 (.leaf 4493205479) (.leaf 4343553757)) (.branch 6 (.leaf 4200329475) (.leaf 4063183699)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3931790782) (.leaf 3805846455)) (.branch 10 (.leaf 3685066122) (.leaf 3569183316))) (.branch 13 (.branch 12 (.leaf 3457948297) (.leaf 3351126795)) (.branch 14 (.leaf 3248498853) (.leaf 3149857785))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3055009220) (.branch 17 (.leaf 2963770228) (.leaf 2875968524))) (.branch 20 (.branch 19 (.leaf 2791441734) (.leaf 2710036725)) (.branch 21 (.leaf 2631608982) (.leaf 2556022041)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2483146965) (.leaf 2412861855)) (.branch 25 (.leaf 2345051403) (.leaf 2279606479))) (.branch 28 (.branch 27 (.leaf 2216423739) (.leaf 2155405277)) (.branch 29 (.leaf 2096458284) (.leaf 2039494748)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1984431161) (.branch 32 (.leaf 1931188252) (.leaf 1879690744))) (.branch 35 (.branch 34 (.leaf 1829867112) (.leaf 1781649375)) (.branch 36 (.leaf 1734972888) (.leaf 1689776155)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1646000649) (.leaf 1603590649)) (.branch 40 (.leaf 1562493083) (.leaf 1522657382))) (.branch 43 (.branch 42 (.leaf 1484035344) (.leaf 1446581007)) (.branch 44 (.leaf 1410250525) (.leaf 1375002057))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1340795662) (.branch 47 (.leaf 1307593197) (.leaf 1275358223))) (.branch 50 (.branch 49 (.leaf 1244055916) (.leaf 1213652987)) (.branch 51 (.leaf 1184117598) (.leaf 1155419294)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1127528927) (.leaf 1100418595)) (.branch 55 (.leaf 1074061577) (.leaf 1048432277))) (.branch 58 (.branch 57 (.leaf 1023506165) (.leaf 999259728)) (.branch 59 (.leaf 975670419) (.leaf 952716609))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 930377547) (.branch 62 (.leaf 908633313) (.leaf 887464781))) (.branch 65 (.branch 64 (.leaf 866853584) (.leaf 846782073)) (.branch 66 (.leaf 827233288) (.leaf 808190924)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 789639302) (.leaf 771563339)) (.branch 70 (.leaf 753948521) (.leaf 736780881))) (.branch 73 (.branch 72 (.leaf 720046969) (.leaf 703733832)) (.branch 74 (.leaf 687828992) (.leaf 672320423))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 657196536) (.branch 77 (.leaf 642446154) (.leaf 628058499))) (.branch 80 (.branch 79 (.leaf 614023171) (.leaf 600330135)) (.branch 81 (.leaf 586969706) (.leaf 573932529)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 561209574) (.leaf 548792112)) (.branch 85 (.leaf 536671713) (.leaf 524840226))) (.branch 88 (.branch 87 (.leaf 513289772) (.leaf 502012731)) (.branch 89 (.leaf 491001732) (.leaf 480249643)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 469749563) (.branch 92 (.leaf 459494811) (.leaf 449478919))) (.branch 95 (.branch 94 (.leaf 439695623) (.leaf 430138853)) (.branch 96 (.leaf 420802731) (.leaf 411681557)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 402769809) (.leaf 394062132)) (.branch 100 (.leaf 385553331) (.leaf 377238371))) (.branch 103 (.branch 102 (.leaf 369112362) (.leaf 361170564)) (.branch 104 (.leaf 353408374) (.leaf 345821324))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 338405074) (.leaf 331155413)) (.branch 108 (.leaf 324068247) (.leaf 317139602))) (.branch 111 (.branch 110 (.leaf 310365615) (.leaf 303742530)) (.branch 112 (.leaf 297266700) (.leaf 290934576)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284742708) (.leaf 278687743)) (.branch 116 (.leaf 272766416) (.leaf 266975554))) (.branch 119 (.branch 118 (.leaf 261312068) (.leaf 255772952)) (.branch 120 (.leaf 250355281) (.leaf 245056208)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 685).q*(generalMeanRows 685).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 685).q*(generalMeanRows 685).cutoff/2-2 = (8026/3883:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable230.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4920964480) (.branch 2 (.leaf 4749573896) (.leaf 4585854694))) (.branch 5 (.branch 4 (.leaf 4429372571) (.leaf 4279723741)) (.branch 6 (.leaf 4136532281) (.leaf 3999447752)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3868143075) (.leaf 3742312623)) (.branch 10 (.leaf 3621670507) (.leaf 3505949028))) (.branch 13 (.branch 12 (.leaf 3394897274) (.leaf 3288279855)) (.branch 14 (.leaf 3185875745) (.leaf 3087477238))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2992888987) (.branch 17 (.leaf 2901927128) (.leaf 2814418484))) (.branch 20 (.branch 19 (.leaf 2730199825) (.leaf 2649117197)) (.branch 21 (.leaf 2571025301) (.leaf 2495786920)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2423272395) (.leaf 2353359133)) (.branch 25 (.leaf 2285931163) (.leaf 2220878714))) (.branch 28 (.branch 27 (.leaf 2158097832) (.leaf 2097490022)) (.branch 29 (.leaf 2038961910) (.leaf 1982424940)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1927795084) (.branch 32 (.leaf 1874992570) (.leaf 1823941639))) (.branch 35 (.branch 34 (.leaf 1774570306) (.leaf 1726810143)) (.branch 36 (.leaf 1680596081) (.leaf 1635866213)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1592561617) (.leaf 1550626197)) (.branch 40 (.leaf 1510006514) (.leaf 1470651654))) (.branch 43 (.branch 42 (.leaf 1432513078) (.leaf 1395544501)) (.branch 44 (.leaf 1359701771) (.leaf 1324942750))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1291227211) (.branch 47 (.leaf 1258516741) (.leaf 1226774637))) (.branch 50 (.branch 49 (.leaf 1195965826) (.leaf 1166056778)) (.branch 51 (.leaf 1137015425) (.leaf 1108811091)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1081414416) (.leaf 1054797298)) (.branch 55 (.leaf 1028932821) (.leaf 1003795203))) (.branch 58 (.branch 57 (.leaf 979359740) (.leaf 955602747)) (.branch 59 (.leaf 932501516) (.leaf 910034267))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 888180098) (.branch 62 (.leaf 866918951) (.leaf 846231567))) (.branch 65 (.branch 64 (.leaf 826099450) (.leaf 806504832)) (.branch 66 (.leaf 787430637) (.leaf 768860451)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 750778491) (.leaf 733169576)) (.branch 70 (.leaf 716019101) (.leaf 699313007))) (.branch 73 (.branch 72 (.leaf 683037764) (.leaf 667180339)) (.branch 74 (.leaf 651728181) (.leaf 636669194))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 621991723) (.branch 77 (.leaf 607684530) (.leaf 593736780))) (.branch 80 (.branch 79 (.leaf 580138018) (.leaf 566878161)) (.branch 81 (.leaf 553947476) (.leaf 541336566)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 529036359) (.leaf 517038093)) (.branch 85 (.leaf 505333300) (.leaf 493913801))) (.branch 88 (.branch 87 (.leaf 482771688) (.leaf 471899316)) (.branch 89 (.leaf 461289292) (.leaf 450934463)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440827911) (.branch 92 (.leaf 430962939) (.leaf 421333066))) (.branch 95 (.branch 94 (.leaf 411932016) (.leaf 402753713)) (.branch 96 (.leaf 393792269) (.leaf 385041981)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 376497322) (.leaf 368152937)) (.branch 100 (.leaf 360003631) (.leaf 352044369))) (.branch 103 (.branch 102 (.leaf 344270268) (.leaf 336676589)) (.branch 104 (.leaf 329258738) (.leaf 322012252))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314932804) (.leaf 308016189)) (.branch 108 (.leaf 301258327) (.leaf 294655256))) (.branch 111 (.branch 110 (.leaf 288203125) (.leaf 281898195)) (.branch 112 (.leaf 275736832) (.leaf 269715506)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263830783) (.leaf 258079329)) (.branch 116 (.leaf 252457897) (.leaf 246963335))) (.branch 119 (.branch 118 (.leaf 241592574) (.leaf 236342630)) (.branch 120 (.leaf 231210598) (.leaf 226193655)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 686).q*(generalMeanRows 686).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 686).q*(generalMeanRows 686).cutoff/2-2 = (8026/3883:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable230.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5305679699) (.branch 2 (.leaf 5138210492) (.leaf 4978067473))) (.branch 5 (.branch 4 (.leaf 4824831728) (.leaf 4678114067)) (.branch 6 (.leaf 4537552425) (.leaf 4402809542)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4273570896) (.leaf 4149542832)) (.branch 10 (.leaf 4030450892) (.leaf 3916038305))) (.branch 13 (.branch 12 (.leaf 3806064610) (.leaf 3700304428)) (.branch 14 (.leaf 3598546324) (.leaf 3500591792))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3406254309) (.branch 17 (.leaf 3315358489) (.leaf 3227739293))) (.branch 20 (.branch 19 (.leaf 3143241319) (.leaf 3061718135)) (.branch 21 (.leaf 2983031679) (.leaf 2907051696)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2833655227) (.leaf 2762726133)) (.branch 25 (.leaf 2694154654) (.leaf 2627837003))) (.branch 28 (.branch 27 (.leaf 2563674988) (.leaf 2501575666)) (.branch 29 (.leaf 2441451015) (.leaf 2383217634)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2326796462) (.branch 32 (.leaf 2272112517) (.leaf 2219094653))) (.branch 35 (.branch 34 (.leaf 2167675334) (.leaf 2117790419)) (.branch 36 (.leaf 2069378971) (.leaf 2022383063)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1976747614) (.leaf 1932420224)) (.branch 40 (.leaf 1889351020) (.leaf 1847492521))) (.branch 43 (.branch 42 (.leaf 1806799499) (.leaf 1767228856)) (.branch 44 (.leaf 1728739509) (.leaf 1691292281))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1654849794) (.branch 47 (.leaf 1619376374) (.leaf 1584837964))) (.branch 50 (.branch 49 (.leaf 1551202031) (.leaf 1518437492)) (.branch 51 (.leaf 1486514636) (.leaf 1455405050)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1425081557) (.leaf 1395518148)) (.branch 55 (.leaf 1366689925) (.leaf 1338573043))) (.branch 58 (.branch 57 (.leaf 1311144658) (.leaf 1284382878)) (.branch 59 (.leaf 1258266713) (.leaf 1232776032))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1207891519) (.branch 62 (.leaf 1183594637) (.leaf 1159867586))) (.branch 65 (.branch 64 (.leaf 1136693270) (.leaf 1114055262)) (.branch 66 (.leaf 1091937774) (.leaf 1070325624)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049204208) (.leaf 1028559477)) (.branch 70 (.leaf 1008377905) (.leaf 988646469))) (.branch 73 (.branch 72 (.leaf 969352626) (.leaf 950484290)) (.branch 74 (.leaf 932029809) (.leaf 913977952))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 896317882) (.branch 77 (.leaf 879039146) (.leaf 862131654))) (.branch 80 (.branch 79 (.leaf 845585663) (.leaf 829391763)) (.branch 81 (.leaf 813540865) (.leaf 798024181)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 782833220) (.leaf 767959766)) (.branch 85 (.leaf 753395874) (.leaf 739133854))) (.branch 88 (.branch 87 (.leaf 725166264) (.leaf 711485898)) (.branch 89 (.leaf 698085775) (.leaf 684959133)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 672099419) (.branch 92 (.leaf 659500279) (.leaf 647155555))) (.branch 95 (.branch 94 (.leaf 635059269) (.leaf 623205626)) (.branch 96 (.leaf 611588999) (.leaf 600203927)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 589045106) (.leaf 578107387)) (.branch 100 (.leaf 567385766) (.leaf 556875380))) (.branch 103 (.branch 102 (.leaf 546571503) (.leaf 536469540)) (.branch 104 (.leaf 526565023) (.leaf 516853606))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 507331060) (.leaf 497993271)) (.branch 108 (.leaf 488836233) (.leaf 479856047))) (.branch 111 (.branch 110 (.leaf 471048916) (.leaf 462411143)) (.branch 112 (.leaf 453939123) (.leaf 445629347)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 437478395) (.leaf 429482930)) (.branch 116 (.leaf 421639703) (.leaf 413945543))) (.branch 119 (.branch 118 (.leaf 406397358) (.leaf 398992133)) (.branch 120 (.leaf 391726924) (.leaf 384598860)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 687).q*(generalMeanRows 687).c/2-2 = (5663/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable205.value]
    have hcontinuation : (generalMeanRows 687).q*(generalMeanRows 687).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5234867497) (.branch 2 (.leaf 5067118971) (.leaf 4906732573))) (.branch 5 (.branch 4 (.leaf 4753287844) (.leaf 4606394127)) (.branch 6 (.leaf 4465687966) (.leaf 4330830779)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4201506781) (.leaf 4077421120)) (.branch 10 (.leaf 3958298190) (.leaf 3843880121))) (.branch 13 (.branch 12 (.leaf 3733925407) (.leaf 3628207662)) (.branch 14 (.leaf 3526514490) (.leaf 3428646456))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3334416154) (.branch 17 (.leaf 3243647342) (.leaf 3156174161))) (.branch 20 (.branch 19 (.leaf 3071840417) (.leaf 2990498918)) (.branch 21 (.leaf 2912010869) (.leaf 2836245307)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2763078593) (.leaf 2692393929)) (.branch 25 (.leaf 2624080918) (.leaf 2558035160))) (.branch 28 (.branch 27 (.leaf 2494157872) (.leaf 2432355537)) (.branch 29 (.leaf 2372539580) (.leaf 2314626064)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2258535410) (.branch 32 (.leaf 2204192137) (.leaf 2151524614))) (.branch 35 (.branch 34 (.leaf 2100464835) (.leaf 2050948209)) (.branch 36 (.leaf 2002913356) (.leaf 1956301927)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1911058431) (.leaf 1867130067)) (.branch 40 (.leaf 1824466581) (.leaf 1783020115))) (.branch 43 (.branch 42 (.leaf 1742745083) (.leaf 1703598037)) (.branch 44 (.leaf 1665537556) (.leaf 1628524135))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1592520081) (.branch 47 (.leaf 1557489412) (.leaf 1523397775))) (.branch 50 (.branch 49 (.leaf 1490212350) (.leaf 1457901776)) (.branch 51 (.leaf 1426436072) (.leaf 1395786568)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1365925833) (.leaf 1336827615)) (.branch 55 (.leaf 1308466782) (.leaf 1280819261))) (.branch 58 (.branch 57 (.leaf 1253861989) (.leaf 1227572861)) (.branch 59 (.leaf 1201930680) (.leaf 1176915119))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1152506669) (.branch 62 (.leaf 1128686609) (.leaf 1105436960))) (.branch 65 (.branch 64 (.leaf 1082740454) (.leaf 1060580497)) (.branch 66 (.leaf 1038941140) (.leaf 1017807046)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 997163463) (.leaf 976996197)) (.branch 70 (.leaf 957291585) (.leaf 938036469))) (.branch 73 (.branch 72 (.leaf 919218177) (.leaf 900824500)) (.branch 74 (.leaf 882843667) (.leaf 865264331))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 848075547) (.branch 77 (.leaf 831266755) (.leaf 814827762))) (.branch 80 (.branch 79 (.leaf 798748730) (.leaf 783020154)) (.branch 81 (.leaf 767632855) (.leaf 752577960)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 737846893) (.leaf 723431362)) (.branch 85 (.leaf 709323344) (.leaf 695515079))) (.branch 88 (.branch 87 (.leaf 681999055) (.leaf 668767998)) (.branch 89 (.leaf 655814868) (.leaf 643132841)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 630715307) (.branch 92 (.leaf 618555859) (.leaf 606648285))) (.branch 95 (.branch 94 (.leaf 594986561) (.leaf 583564843)) (.branch 96 (.leaf 572377462) (.leaf 561418915)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 550683859) (.leaf 540167108)) (.branch 100 (.leaf 529863622) (.leaf 519768508))) (.branch 103 (.branch 102 (.leaf 509877007) (.leaf 500184497)) (.branch 104 (.leaf 490686483) (.leaf 481378595))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 472256580) (.leaf 463316302)) (.branch 108 (.leaf 454553738) (.leaf 445964969))) (.branch 111 (.branch 110 (.leaf 437546184) (.leaf 429293668)) (.branch 112 (.leaf 421203806) (.leaf 413273077)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 405498048) (.leaf 397875377)) (.branch 116 (.leaf 390401804) (.leaf 383074153))) (.branch 119 (.branch 118 (.leaf 375889327) (.leaf 368844305)) (.branch 120 (.leaf 361936144) (.leaf 355161968)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 688).q*(generalMeanRows 688).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 688).q*(generalMeanRows 688).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5304550411) (.branch 2 (.leaf 5137114629) (.leaf 4977016676))) (.branch 5 (.branch 4 (.leaf 4823836017) (.leaf 4677181997)) (.branch 6 (.leaf 4536691224) (.leaf 4402025244)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4272868455) (.leaf 4148926234)) (.branch 10 (.leaf 4029923250) (.leaf 3915601949))) (.branch 13 (.branch 12 (.leaf 3805721173) (.leaf 3700054913)) (.branch 14 (.leaf 3598391181) (.leaf 3500530974))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3406287331) (.branch 17 (.leaf 3315484481) (.leaf 3227957046))) (.branch 20 (.branch 19 (.leaf 3143549326) (.leaf 3062114633)) (.branch 21 (.leaf 2983514683) (.leaf 2907619032)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2834304562) (.leaf 2763454998)) (.branch 25 (.leaf 2694960471) (.leaf 2628717106))) (.branch 28 (.branch 27 (.leaf 2564626643) (.leaf 2502596088)) (.branch 29 (.leaf 2442537383) (.leaf 2384367106)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2328006187) (.branch 32 (.leaf 2273379649) (.leaf 2220416358))) (.branch 35 (.branch 34 (.leaf 2169048798) (.leaf 2119212861)) (.branch 36 (.leaf 2070847642) (.leaf 2023895262)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1978300684) (.leaf 1934011562)) (.branch 40 (.leaf 1890978079) (.leaf 1849152813))) (.branch 43 (.branch 42 (.leaf 1808490597) (.leaf 1768948400)) (.branch 44 (.leaf 1730485204) (.leaf 1693061898))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1656641173) (.branch 47 (.leaf 1621187426) (.leaf 1586666667))) (.branch 50 (.branch 49 (.leaf 1553046434) (.leaf 1520295713)) (.branch 51 (.leaf 1488384862) (.leaf 1457285537)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1426970627) (.leaf 1397414192)) (.branch 55 (.leaf 1368591399) (.leaf 1340478469))) (.branch 58 (.branch 57 (.leaf 1313052621) (.leaf 1286292025)) (.branch 59 (.leaf 1260175753) (.leaf 1234683733))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1209796708) (.branch 62 (.leaf 1185496198) (.leaf 1161764459))) (.branch 65 (.branch 64 (.leaf 1138584447) (.leaf 1115939789)) (.branch 66 (.leaf 1093814746) (.leaf 1072194187)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1051063556) (.leaf 1030408847)) (.branch 70 (.leaf 1010216582) (.leaf 990473781))) (.branch 73 (.branch 72 (.leaf 971167941) (.leaf 952287016)) (.branch 74 (.leaf 933819394) (.leaf 915753879))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 898079673) (.branch 77 (.leaf 880786356) (.leaf 863863870))) (.branch 80 (.branch 79 (.leaf 847302505) (.leaf 831092882)) (.branch 81 (.leaf 815225939) (.leaf 799692920)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 784485356) (.leaf 769595060)) (.branch 85 (.leaf 755014110) (.leaf 740734841))) (.branch 88 (.branch 87 (.leaf 726749832) (.leaf 713051899)) (.branch 89 (.leaf 699634081) (.leaf 686489635)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 673612028) (.branch 92 (.leaf 660994922) (.leaf 648632176))) (.branch 95 (.branch 94 (.leaf 636517829) (.leaf 624646099)) (.branch 96 (.leaf 613011375) (.leaf 601608209)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 590431310) (.leaf 579475540)) (.branch 100 (.leaf 568735908) (.leaf 558207560))) (.branch 103 (.branch 102 (.leaf 547885782) (.leaf 537765987)) (.branch 104 (.leaf 527843718) (.leaf 518114635))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 508574519) (.leaf 499219261)) (.branch 108 (.leaf 490044864) (.leaf 481047436))) (.branch 111 (.branch 110 (.leaf 472223184) (.leaf 463568416)) (.branch 112 (.leaf 455079535) (.leaf 446753036)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 438585501) (.leaf 430573600)) (.branch 116 (.leaf 422714087) (.leaf 415003793))) (.branch 119 (.branch 118 (.leaf 407439631) (.leaf 400018587)) (.branch 120 (.leaf 392737722) (.leaf 385594165)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 689).q*(generalMeanRows 689).c/2-2 = (5663/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable205.value]
    have hcontinuation : (generalMeanRows 689).q*(generalMeanRows 689).cutoff/2-2 = (32058/15179:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable233.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5233402587) (.branch 2 (.leaf 5065691256) (.leaf 4905353572))) (.branch 5 (.branch 4 (.leaf 4751967463) (.leaf 4605140815)) (.branch 6 (.leaf 4464508855) (.leaf 4329731812)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4200492833) (.leaf 4076496098)) (.branch 10 (.leaf 3957465137) (.leaf 3843141303))) (.branch 13 (.branch 12 (.leaf 3733282396) (.leaf 3627661407)) (.branch 14 (.leaf 3526065388) (.leaf 3428294414))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3334160643) (.branch 17 (.leaf 3243487451) (.leaf 3156108642))) (.branch 20 (.branch 19 (.leaf 3071867730) (.leaf 2990617268)) (.branch 21 (.leaf 2912218240) (.leaf 2836539498)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2763457243) (.leaf 2692854545)) (.branch 25 (.leaf 2624620900) (.leaf 2558651821))) (.branch 28 (.branch 27 (.leaf 2494848458) (.leaf 2433117243)) (.branch 29 (.leaf 2373369566) (.leaf 2315521473)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2259493376) (.branch 32 (.leaf 2205209796) (.leaf 2152599118))) (.branch 35 (.branch 34 (.leaf 2101593358) (.leaf 2052127954)) (.branch 36 (.leaf 2004141564) (.leaf 1957575883)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1912375466) (.leaf 1868487566)) (.branch 40 (.leaf 1825861985) (.leaf 1784450926))) (.branch 43 (.branch 42 (.leaf 1744208862) (.leaf 1705092413)) (.branch 44 (.leaf 1667060223) (.leaf 1630072855))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1594092682) (.branch 47 (.leaf 1559083795) (.leaf 1525011907))) (.branch 50 (.branch 49 (.leaf 1491844269) (.leaf 1459549591)) (.branch 51 (.leaf 1428097959) (.leaf 1397460771)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1367610665) (.leaf 1338521457)) (.branch 55 (.leaf 1310168078) (.leaf 1282526522))) (.branch 58 (.branch 57 (.leaf 1255573790) (.leaf 1229287837)) (.branch 59 (.leaf 1203647530) (.leaf 1178632600))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1154223597) (.branch 62 (.leaf 1130401856) (.leaf 1107149454))) (.branch 65 (.branch 64 (.leaf 1084449176) (.leaf 1062284481)) (.branch 66 (.leaf 1040639471) (.leaf 1019498857)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 998847936) (.leaf 978672559)) (.branch 70 (.leaf 958959107) (.leaf 939694466))) (.branch 73 (.branch 72 (.leaf 920866006) (.leaf 902461556)) (.branch 74 (.leaf 884469387) (.leaf 866878186))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 849677044) (.branch 77 (.leaf 832855437) (.leaf 816403205))) (.branch 80 (.branch 79 (.leaf 800310540) (.leaf 784567969)) (.branch 81 (.leaf 769166341) (.leaf 754096813)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 739350833) (.leaf 724920136)) (.branch 85 (.leaf 710796724) (.leaf 696972860))) (.branch 88 (.branch 87 (.leaf 683441054) (.leaf 670194054)) (.branch 89 (.leaf 657224839) (.leaf 644526606)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 632092763) (.branch 92 (.leaf 619916919) (.leaf 607992881))) (.branch 95 (.branch 94 (.leaf 596314640) (.leaf 584876367)) (.branch 96 (.leaf 573672406) (.leaf 562697269)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 551945626) (.leaf 541412302)) (.branch 100 (.leaf 531092270) (.leaf 520980645))) (.branch 103 (.branch 102 (.leaf 511072681) (.leaf 501363764)) (.branch 104 (.leaf 491849409) (.leaf 482525253))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 473387052) (.leaf 464430678)) (.branch 108 (.leaf 455652114) (.leaf 447047448))) (.branch 111 (.branch 110 (.leaf 438612873) (.leaf 430344684)) (.branch 112 (.leaf 422239268) (.leaf 414293108)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 406502779) (.leaf 398864939)) (.branch 116 (.leaf 391376335) (.leaf 384033793))) (.branch 119 (.branch 118 (.leaf 376834220) (.leaf 369774598)) (.branch 120 (.leaf 362851984) (.leaf 356063508)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 690).q*(generalMeanRows 690).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 690).q*(generalMeanRows 690).cutoff/2-2 = (32058/15179:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable233.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5165428963) (.branch 2 (.leaf 4997438274) (.leaf 4836845416))) (.branch 5 (.branch 4 (.leaf 4683228349) (.leaf 4536194919)) (.branch 6 (.leaf 4395380247) (.leaf 4260444400)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4131070308) (.leaf 4006961892)) (.branch 10 (.leaf 3887842377) (.leaf 3773452776))) (.branch 13 (.branch 12 (.leaf 3663550514) (.leaf 3557908180)) (.branch 14 (.leaf 3456312399) (.leaf 3358562797))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3264471062) (.branch 17 (.leaf 3173860087) (.leaf 3086563181))) (.branch 20 (.branch 19 (.leaf 3002423348) (.leaf 2921292624)) (.branch 21 (.leaf 2843031471) (.leaf 2767508214)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2694598520) (.leaf 2624184929)) (.branch 25 (.leaf 2556156404) (.leaf 2490407925))) (.branch 28 (.branch 27 (.leaf 2426840112) (.leaf 2365358874)) (.branch 29 (.leaf 2305875077) (.leaf 2248304248)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2192566289) (.branch 32 (.leaf 2138585218) (.leaf 2086288918))) (.branch 35 (.branch 34 (.leaf 2035608917) (.leaf 1986480169)) (.branch 36 (.leaf 1938840858) (.leaf 1892632212)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1847798330) (.leaf 1804286018)) (.branch 40 (.leaf 1762044637) (.leaf 1721025963))) (.branch 43 (.branch 42 (.leaf 1681184049) (.leaf 1642475105)) (.branch 44 (.leaf 1604857375) (.leaf 1568291032))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1532738069) (.branch 47 (.leaf 1498162205) (.leaf 1464528795))) (.branch 50 (.branch 49 (.leaf 1431804738) (.leaf 1399958400)) (.branch 51 (.leaf 1368959539) (.leaf 1338779229)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1309389795) (.leaf 1280764750)) (.branch 55 (.leaf 1252878731) (.leaf 1225707446))) (.branch 58 (.branch 57 (.leaf 1199227619) (.leaf 1173416938)) (.branch 59 (.leaf 1148254011) (.leaf 1123718317))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1099790166) (.branch 62 (.leaf 1076450656) (.leaf 1053681639))) (.branch 65 (.branch 64 (.leaf 1031465681) (.leaf 1009786031)) (.branch 66 (.leaf 988626585) (.leaf 967971861)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 947806965) (.leaf 928117566)) (.branch 70 (.leaf 908889870) (.leaf 890110595))) (.branch 73 (.branch 72 (.leaf 871766947) (.leaf 853846600)) (.branch 74 (.leaf 836337675) (.leaf 819228715))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 802508674) (.branch 77 (.leaf 786166894) (.leaf 770193088))) (.branch 80 (.branch 79 (.leaf 754577328) (.leaf 739310023)) (.branch 81 (.leaf 724381913) (.leaf 709784045)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 695507769) (.leaf 681544721)) (.branch 85 (.leaf 667886811) (.leaf 654526213))) (.branch 88 (.branch 87 (.leaf 641455354) (.leaf 628666903)) (.branch 89 (.leaf 616153762) (.leaf 603909055)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 591926124) (.branch 92 (.leaf 580198512) (.leaf 568719965))) (.branch 95 (.branch 94 (.leaf 557484416) (.leaf 546485983)) (.branch 96 (.leaf 535718958) (.leaf 525177804)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 514857146) (.leaf 504751767)) (.branch 100 (.leaf 494856601) (.leaf 485166725))) (.branch 103 (.branch 102 (.leaf 475677359) (.leaf 466383858)) (.branch 104 (.leaf 457281707) (.leaf 448366516))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 439634017) (.leaf 431080058)) (.branch 108 (.leaf 422700602) (.leaf 414491720))) (.branch 111 (.branch 110 (.leaf 406449587) (.leaf 398570483)) (.branch 112 (.leaf 390850784) (.leaf 383286961)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 375875578) (.leaf 368613288)) (.branch 116 (.leaf 361496831) (.leaf 354523027))) (.branch 119 (.branch 118 (.leaf 347688781) (.leaf 340991073)) (.branch 120 (.leaf 334426960) (.leaf 327993571)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 691).q*(generalMeanRows 691).c/2-2 = (1199/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable178.value]
    have hcontinuation : (generalMeanRows 691).q*(generalMeanRows 691).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5183229130) (.branch 2 (.leaf 5014659542) (.leaf 4853513279))) (.branch 5 (.branch 4 (.leaf 4699366845) (.leaf 4551826734)) (.branch 6 (.leaf 4410526812) (.leaf 4275125973)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4145306056) (.leaf 4020769960)) (.branch 10 (.leaf 3901239957) (.leaf 3786456167))) (.branch 13 (.branch 12 (.leaf 3676175179) (.leaf 3570168800)) (.branch 14 (.leaf 3468222918) (.leaf 3370136469))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3275720492) (.branch 17 (.leaf 3184797270) (.leaf 3097199538))) (.branch 20 (.branch 19 (.leaf 3012769757) (.leaf 2931359455)) (.branch 21 (.leaf 2852828613) (.leaf 2777045100)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2703884159) (.leaf 2633227921)) (.branch 25 (.leaf 2564964968) (.leaf 2498989918))) (.branch 28 (.branch 27 (.leaf 2435203050) (.leaf 2373509946)) (.branch 29 (.leaf 2313821166) (.leaf 2256051947)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2200121915) (.branch 32 (.leaf 2145954824) (.leaf 2093478310))) (.branch 35 (.branch 34 (.leaf 2042623664) (.leaf 1993325618)) (.branch 36 (.leaf 1945522141) (.leaf 1899154259)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1854165879) (.leaf 1810503622)) (.branch 40 (.leaf 1768116677) (.leaf 1726956651))) (.branch 43 (.branch 42 (.leaf 1686977442) (.leaf 1648135106)) (.branch 44 (.leaf 1610387745) (.leaf 1573695393))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1538019914) (.branch 47 (.leaf 1503324901) (.leaf 1469575589))) (.branch 50 (.branch 49 (.leaf 1436738764) (.leaf 1404782683)) (.branch 51 (.leaf 1373677000) (.leaf 1343392688)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1313901978) (.leaf 1285178290)) (.branch 55 (.leaf 1257196176) (.leaf 1229931258))) (.branch 58 (.branch 57 (.leaf 1203360180) (.leaf 1177460556)) (.branch 59 (.leaf 1152210917) (.leaf 1127590672))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1103580064) (.branch 62 (.leaf 1080160126) (.leaf 1057312646))) (.branch 65 (.branch 64 (.leaf 1035020132) (.leaf 1013265773)) (.branch 66 (.leaf 992033412) (.leaf 971307511)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 951073126) (.leaf 931315877)) (.branch 70 (.leaf 912021922) (.leaf 893177933))) (.branch 73 (.branch 72 (.leaf 874771073) (.leaf 856788972)) (.branch 74 (.leaf 839219710) (.leaf 822051793))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 805274134) (.branch 77 (.leaf 788876040) (.leaf 772847188))) (.branch 80 (.branch 79 (.leaf 757177616) (.leaf 741857700)) (.branch 81 (.leaf 726878147) (.leaf 712229974)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 697904502) (.leaf 683893337)) (.branch 85 (.leaf 670188362) (.leaf 656781723))) (.branch 88 (.branch 87 (.leaf 643665821) (.leaf 630833301)) (.branch 89 (.leaf 618277039) (.leaf 605990137)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 593965912) (.branch 92 (.leaf 582197888) (.leaf 570679785))) (.branch 95 (.branch 94 (.leaf 559405519) (.leaf 548369184)) (.branch 96 (.leaf 537565056) (.leaf 526987577)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516631354) (.leaf 506491152)) (.branch 100 (.leaf 496561886) (.leaf 486838619))) (.branch 103 (.branch 102 (.leaf 477316552) (.leaf 467991026)) (.branch 104 (.leaf 458857509) (.leaf 449911596))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 441149004) (.leaf 432565568)) (.branch 108 (.leaf 424157237) (.leaf 415920066))) (.branch 111 (.branch 110 (.leaf 407850221) (.leaf 399943965)) (.branch 112 (.leaf 392197663) (.leaf 384607775)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 377170852) (.leaf 369883537)) (.branch 116 (.leaf 362742556) (.leaf 355744721))) (.branch 119 (.branch 118 (.leaf 348886923) (.leaf 342166135)) (.branch 120 (.leaf 335579402) (.leaf 329123844)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 692).q*(generalMeanRows 692).c/2-2 = (1199/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable178.value]
    have hcontinuation : (generalMeanRows 692).q*(generalMeanRows 692).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5052302938) (.branch 2 (.leaf 4883283509) (.leaf 4721734416))) (.branch 5 (.branch 4 (.leaf 4567232123) (.leaf 4419382951)) (.branch 6 (.leaf 4277820473) (.leaf 4142203186)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4012212430) (.leaf 3887550521)) (.branch 10 (.leaf 3767939072) (.leaf 3653117476))) (.branch 13 (.branch 12 (.leaf 3542841531) (.leaf 3436882206)) (.branch 14 (.leaf 3335024502) (.leaf 3237066429))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3142818070) (.branch 17 (.leaf 3052100720) (.leaf 2964746103))) (.branch 20 (.branch 19 (.leaf 2880595656) (.leaf 2799499864)) (.branch 21 (.leaf 2721317654) (.leaf 2645915838)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2573168595) (.leaf 2502956992)) (.branch 25 (.leaf 2435168550) (.leaf 2369696829))) (.branch 28 (.branch 27 (.leaf 2306441055) (.leaf 2245305767)) (.branch 29 (.leaf 2186200492) (.leaf 2129039443)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2073741236) (.branch 32 (.leaf 2020228630) (.leaf 1968428282))) (.branch 35 (.branch 34 (.leaf 1918270516) (.leaf 1869689115)) (.branch 36 (.leaf 1822621120) (.leaf 1777006643)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1732788696) (.leaf 1689913028)) (.branch 40 (.leaf 1648327969) (.leaf 1607984293))) (.branch 43 (.branch 42 (.leaf 1568835079) (.leaf 1530835588)) (.branch 44 (.leaf 1493943145) (.leaf 1458117029))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1423318366) (.branch 47 (.leaf 1389510035) (.leaf 1356656572))) (.branch 50 (.branch 49 (.leaf 1324724087) (.leaf 1293680180)) (.branch 51 (.leaf 1263493866) (.leaf 1234135502)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1205576717) (.leaf 1177790351)) (.branch 55 (.leaf 1150750392) (.leaf 1124431920))) (.branch 58 (.branch 57 (.leaf 1098811050) (.leaf 1073864887)) (.branch 59 (.leaf 1049571472) (.leaf 1025909737))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1002859467) (.branch 62 (.leaf 980401252) (.leaf 958516456))) (.branch 65 (.branch 64 (.leaf 937187172) (.leaf 916396196)) (.branch 66 (.leaf 896126990) (.leaf 876363648)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 857090876) (.leaf 838293952)) (.branch 70 (.leaf 819958711) (.leaf 802071513))) (.branch 73 (.branch 72 (.leaf 784619220) (.leaf 767589178)) (.branch 74 (.leaf 750969190) (.leaf 734747498))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718912766) (.branch 77 (.leaf 703454058) (.leaf 688360824))) (.branch 80 (.branch 79 (.leaf 673622880) (.leaf 659230395)) (.branch 81 (.leaf 645173875) (.leaf 631444149)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618032357) (.leaf 604929934)) (.branch 85 (.leaf 592128600) (.leaf 579620347))) (.branch 88 (.branch 87 (.leaf 567397432) (.leaf 555452360)) (.branch 89 (.leaf 543777877) (.leaf 532366964)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521212820) (.branch 92 (.leaf 510308861) (.leaf 499648709))) (.branch 95 (.branch 94 (.leaf 489226179) (.leaf 479035281)) (.branch 96 (.leaf 469070205) (.leaf 459325317)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 449795153) (.leaf 440474411)) (.branch 100 (.leaf 431357947) (.leaf 422440768))) (.branch 103 (.branch 102 (.leaf 413718025) (.leaf 405185012)) (.branch 104 (.leaf 396837156) (.leaf 388670016))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 380679277) (.leaf 372860744)) (.branch 108 (.leaf 365210341) (.leaf 357724105))) (.branch 111 (.branch 110 (.leaf 350398182) (.leaf 343228823)) (.branch 112 (.leaf 336212383) (.leaf 329345314)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 322624164) (.leaf 316045573)) (.branch 116 (.leaf 309606271) (.leaf 303303074))) (.branch 119 (.branch 118 (.leaf 297132881) (.leaf 291092673)) (.branch 120 (.leaf 285179508) (.leaf 279390522)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 693).q*(generalMeanRows 693).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 693).q*(generalMeanRows 693).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5116913811) (.branch 2 (.leaf 4948099809) (.leaf 4786732968))) (.branch 5 (.branch 4 (.leaf 4632389785) (.leaf 4484676681)) (.branch 6 (.leaf 4343227382) (.leaf 4207700594)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4077777914) (.leaf 3953161955)) (.branch 10 (.leaf 3833574665) (.leaf 3718755806))) (.branch 13 (.branch 12 (.leaf 3608461575) (.leaf 3502463362)) (.branch 14 (.leaf 3400546615) (.leaf 3302509808))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3208163503) (.branch 17 (.leaf 3117329490) (.leaf 3029839998))) (.branch 20 (.branch 19 (.leaf 2945536976) (.leaf 2864271429)) (.branch 21 (.leaf 2785902811) (.leaf 2710298459)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2637333083) (.leaf 2566888281)) (.branch 25 (.leaf 2498852100) (.leaf 2433118627))) (.branch 28 (.branch 27 (.leaf 2369587611) (.leaf 2308164109)) (.branch 29 (.leaf 2248758162) (.leaf 2191284490)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2135662212) (.branch 32 (.leaf 2081814579) (.leaf 2029668734))) (.branch 35 (.branch 34 (.leaf 1979155481) (.leaf 1930209071)) (.branch 36 (.leaf 1882767006) (.leaf 1836769851)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1792161059) (.leaf 1748886812)) (.branch 40 (.leaf 1706895864) (.leaf 1666139400))) (.branch 43 (.branch 42 (.leaf 1626570905) (.leaf 1588146031)) (.branch 44 (.leaf 1550822488) (.leaf 1514559927))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1479319837) (.branch 47 (.leaf 1445065450) (.leaf 1411761646))) (.branch 50 (.branch 49 (.leaf 1379374868) (.leaf 1347873040)) (.branch 51 (.leaf 1317225490) (.leaf 1287402879)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1258377132) (.leaf 1230121373)) (.branch 55 (.leaf 1202609868) (.leaf 1175817962))) (.branch 58 (.branch 57 (.leaf 1149722030) (.leaf 1124299426)) (.branch 59 (.leaf 1099528431) (.leaf 1075388212))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1051858776) (.branch 62 (.leaf 1028920931) (.leaf 1006556247))) (.branch 65 (.branch 64 (.leaf 984747020) (.leaf 963476238)) (.branch 66 (.leaf 942727549) (.leaf 922485226)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 902734145) (.leaf 883459750)) (.branch 70 (.leaf 864648034) (.leaf 846285507))) (.branch 73 (.branch 72 (.leaf 828359178) (.leaf 810856530)) (.branch 74 (.leaf 793765500) (.leaf 777074458))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760772188) (.branch 77 (.leaf 744847871) (.leaf 729291067))) (.branch 80 (.branch 79 (.leaf 714091697) (.leaf 699240031)) (.branch 81 (.leaf 684726671) (.leaf 670542536)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 656678852) (.leaf 643127136)) (.branch 85 (.leaf 629879184) (.leaf 616927064))) (.branch 88 (.branch 87 (.leaf 604263100) (.leaf 591879862)) (.branch 89 (.leaf 579770158) (.leaf 567927027)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 556343722) (.branch 92 (.leaf 545013710) (.leaf 533930658))) (.branch 95 (.branch 94 (.leaf 523088428) (.leaf 512481071)) (.branch 96 (.leaf 502102813) (.leaf 491948057)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 482011371) (.leaf 472287483)) (.branch 100 (.leaf 462771275) (.leaf 453457780))) (.branch 103 (.branch 102 (.leaf 444342170) (.leaf 435419760)) (.branch 104 (.leaf 426685994) (.leaf 418136447))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 409766816) (.leaf 401572920)) (.branch 108 (.leaf 393550691) (.leaf 385696174))) (.branch 111 (.branch 110 (.leaf 378005520) (.leaf 370474986)) (.branch 112 (.leaf 363100928) (.leaf 355879800)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 348808149) (.leaf 341882614)) (.branch 116 (.leaf 335099921) (.leaf 328456881))) (.branch 119 (.branch 118 (.leaf 321950388) (.leaf 315577416)) (.branch 120 (.leaf 309335014) (.leaf 303220308)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 694).q*(generalMeanRows 694).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 694).q*(generalMeanRows 694).cutoff/2-2 = (31886/15265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable235.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5050225782) (.branch 2 (.leaf 4881235149) (.leaf 4719727063))) (.branch 5 (.branch 4 (.leaf 4565276360) (.leaf 4417487885)) (.branch 6 (.leaf 4275993876) (.leaf 4140451620)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4010541367) (.leaf 3885964449)) (.branch 10 (.leaf 3766441591) (.leaf 3651711389))) (.branch 13 (.branch 12 (.leaf 3541528926) (.leaf 3435664528)) (.branch 14 (.leaf 3333902622) (.leaf 3236040709))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3141888415) (.branch 17 (.leaf 3051266633) (.leaf 2964006732))) (.branch 20 (.branch 19 (.leaf 2879949835) (.leaf 2798946156)) (.branch 21 (.leaf 2720854383) (.leaf 2645541124)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2572880381) (.leaf 2502753075)) (.branch 25 (.leaf 2435046600) (.leaf 2369654415))) (.branch 28 (.branch 27 (.leaf 2306475664) (.leaf 2245414820)) (.branch 29 (.leaf 2186381363) (.leaf 2129289472)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2074057744) (.branch 32 (.leaf 2020608927) (.leaf 1968869680))) (.branch 35 (.branch 34 (.leaf 1918770339) (.leaf 1870244705)) (.branch 36 (.leaf 1823229846) (.leaf 1777665908)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1733495940) (.leaf 1690665735)) (.branch 40 (.leaf 1649123671) (.leaf 1608820572))) (.branch 43 (.branch 42 (.leaf 1569709572) (.leaf 1531745990)) (.branch 44 (.leaf 1494887209) (.leaf 1459092569))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1424323257) (.branch 47 (.leaf 1390542216) (.leaf 1357714045))) (.branch 50 (.branch 49 (.leaf 1325804918) (.leaf 1294782500)) (.branch 51 (.leaf 1264615869) (.leaf 1235275446)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1206732924) (.leaf 1178961205)) (.branch 55 (.leaf 1151934340) (.leaf 1125627468))) (.branch 58 (.branch 57 (.leaf 1100016768) (.leaf 1075079400)) (.branch 59 (.leaf 1050793465) (.leaf 1027137952))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1004092701) (.branch 62 (.leaf 981638357) (.leaf 959756336))) (.branch 65 (.branch 64 (.leaf 938428783) (.leaf 917638545)) (.branch 66 (.leaf 897369130) (.leaf 877604684)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 858329954) (.leaf 839530266)) (.branch 70 (.leaf 821191497) (.leaf 803300048))) (.branch 73 (.branch 72 (.leaf 785842823) (.leaf 768807205)) (.branch 74 (.leaf 752181036) (.leaf 735952595))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 720110579) (.branch 77 (.leaf 704644087) (.leaf 689542600))) (.branch 80 (.branch 79 (.leaf 674795966) (.leaf 660394385)) (.branch 81 (.leaf 646328390) (.leaf 632588839)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 619166897) (.leaf 606054024)) (.branch 85 (.leaf 593241967) (.leaf 580722739))) (.branch 88 (.branch 87 (.leaf 568488620) (.leaf 556532135)) (.branch 89 (.leaf 544846052) (.leaf 533423369)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522257307) (.branch 92 (.leaf 511341297) (.leaf 500668978))) (.branch 95 (.branch 94 (.leaf 490234182) (.leaf 480030932)) (.branch 96 (.leaf 470053435) (.leaf 460296069)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450753383) (.leaf 441420089)) (.branch 100 (.leaf 432291053) (.leaf 423361292))) (.branch 103 (.branch 102 (.leaf 414625971) (.leaf 406080390)) (.branch 104 (.leaf 397719988) (.leaf 389540331))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381537113) (.leaf 373706147)) (.branch 108 (.leaf 366043364) (.leaf 358544807))) (.branch 111 (.branch 110 (.leaf 351206629) (.leaf 344025089)) (.branch 112 (.leaf 336996544) (.leaf 330117453)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 323384369) (.leaf 316793936)) (.branch 116 (.leaf 310342889) (.leaf 304028046))) (.branch 119 (.branch 118 (.leaf 297846312) (.leaf 291794670)) (.branch 120 (.leaf 285870180) (.leaf 280069982)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 695).q*(generalMeanRows 695).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 695).q*(generalMeanRows 695).cutoff/2-2 = (31886/15265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable235.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5070005641) (.branch 2 (.leaf 4900393988) (.leaf 4738278845))) (.branch 5 (.branch 4 (.leaf 4583235193) (.leaf 4434867974)) (.branch 6 (.leaf 4292809477) (.leaf 4156717002)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4026270773) (.leaf 3901172063)) (.branch 10 (.leaf 3781141509) (.leaf 3665917590))) (.branch 13 (.branch 12 (.leaf 3555255251) (.leaf 3448924656)) (.branch 14 (.leaf 3346710054) (.leaf 3248408748))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3153830153) (.branch 17 (.leaf 3062794939) (.leaf 2975134242))) (.branch 20 (.branch 19 (.leaf 2890688941) (.leaf 2809308998)) (.branch 21 (.leaf 2730852846) (.leaf 2655186831)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2582184689) (.leaf 2511727073)) (.branch 25 (.leaf 2443701108) (.leaf 2377999982))) (.branch 28 (.branch 27 (.leaf 2314522566) (.leaf 2253173067)) (.branch 29 (.leaf 2193860694) (.leaf 2136499358)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2081007393) (.branch 32 (.leaf 2027307285) (.leaf 1975325434))) (.branch 35 (.branch 34 (.leaf 1924991921) (.leaf 1876240296)) (.branch 36 (.leaf 1829007380) (.leaf 1783233075)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1738860194) (.leaf 1695834294)) (.branch 40 (.leaf 1654103526) (.leaf 1613618490))) (.branch 43 (.branch 42 (.leaf 1574332101) (.leaf 1536199464)) (.branch 44 (.leaf 1499177755) (.leaf 1463226108))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1428305515) (.branch 47 (.leaf 1394378723) (.leaf 1361410145))) (.branch 50 (.branch 49 (.leaf 1329365772) (.leaf 1298213091)) (.branch 51 (.leaf 1267921007) (.leaf 1238459774)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1209800923) (.leaf 1181917197)) (.branch 55 (.leaf 1154782493) (.leaf 1128371803))) (.branch 58 (.branch 57 (.leaf 1102661161) (.leaf 1077627590)) (.branch 59 (.leaf 1053249053) (.leaf 1029504410))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1006373374) (.branch 62 (.leaf 983836469) (.leaf 961874990))) (.branch 65 (.branch 64 (.leaf 940470971) (.leaf 919607146)) (.branch 66 (.leaf 899266918) (.leaf 879434329)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 860094026) (.leaf 841231240)) (.branch 70 (.leaf 822831755) (.leaf 804881881))) (.branch 73 (.branch 72 (.leaf 787368438) (.leaf 770278724)) (.branch 74 (.leaf 753600501) (.leaf 737321971))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 721431756) (.branch 77 (.leaf 705918883) (.leaf 690772763))) (.branch 80 (.branch 79 (.leaf 675983179) (.leaf 661540264)) (.branch 81 (.leaf 647434492) (.leaf 633656659)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 620197873) (.leaf 607049541)) (.branch 85 (.leaf 594203352) (.leaf 581651272))) (.branch 88 (.branch 87 (.leaf 569385529) (.leaf 557398603)) (.branch 89 (.leaf 545683214) (.leaf 534232318)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 523039091) (.branch 92 (.leaf 512096927) (.leaf 501399422))) (.branch 95 (.branch 94 (.leaf 490940373) (.leaf 480713767)) (.branch 96 (.leaf 470713774) (.leaf 460934741)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451371185) (.leaf 442017784)) (.branch 100 (.leaf 432869377) (.leaf 423920953))) (.branch 103 (.branch 102 (.leaf 415167647) (.leaf 406604735)) (.branch 104 (.leaf 398227629) (.leaf 390031872))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382013134) (.leaf 374167206)) (.branch 108 (.leaf 366489997) (.leaf 358977530))) (.branch 111 (.branch 110 (.leaf 351625938) (.leaf 344431459)) (.branch 112 (.leaf 337390434) (.leaf 330499303)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 323754603) (.leaf 317152961)) (.branch 116 (.leaf 310691097) (.leaf 304365814))) (.branch 119 (.branch 118 (.leaf 298174001) (.leaf 292112629)) (.branch 120 (.leaf 286178745) (.leaf 280369475)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 696).q*(generalMeanRows 696).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 696).q*(generalMeanRows 696).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5004693283) (.branch 2 (.leaf 4834933357) (.leaf 4672705259))) (.branch 5 (.branch 4 (.leaf 4517582262) (.leaf 4369167692)) (.branch 6 (.leaf 4227092304) (.leaf 4091011946)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3960605458) (.leaf 3835572801)) (.branch 10 (.leaf 3715633359) (.leaf 3600524416))) (.branch 13 (.branch 12 (.leaf 3489999780) (.leaf 3383828525)) (.branch 14 (.leaf 3281793859) (.leaf 3183692092))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3089331685) (.branch 17 (.leaf 2998532395) (.leaf 2911124482))) (.branch 20 (.branch 19 (.leaf 2826947987) (.leaf 2745852066)) (.branch 21 (.leaf 2667694380) (.leaf 2592340530)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2519663541) (.leaf 2449543379)) (.branch 25 (.leaf 2381866510) (.leaf 2316525488))) (.branch 28 (.branch 27 (.leaf 2253418576) (.leaf 2192449391)) (.branch 29 (.leaf 2133526580) (.leaf 2076563511)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2021477993) (.branch 32 (.leaf 1968192010) (.leaf 1916631477))) (.branch 35 (.branch 34 (.leaf 1866726009) (.leaf 1818408706)) (.branch 36 (.leaf 1771615956) (.leaf 1726287245)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1682364986) (.leaf 1639794348)) (.branch 40 (.leaf 1598523111) (.leaf 1558501518))) (.branch 43 (.branch 42 (.leaf 1519682138) (.leaf 1482019745)) (.branch 44 (.leaf 1445471196) (.leaf 1409995317))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1375552805) (.branch 47 (.leaf 1342106124) (.leaf 1309619411))) (.branch 50 (.branch 49 (.leaf 1278058396) (.leaf 1247390313)) (.branch 51 (.leaf 1217583824) (.leaf 1188608948)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1160436992) (.leaf 1133040485)) (.branch 55 (.leaf 1106393117) (.leaf 1080469681))) (.branch 58 (.branch 57 (.leaf 1055246020) (.leaf 1030698974)) (.branch 59 (.leaf 1006806332) (.leaf 983546785))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 960899886) (.branch 62 (.leaf 938846004) (.leaf 917366287))) (.branch 65 (.branch 64 (.leaf 896442629) (.leaf 876057628)) (.branch 66 (.leaf 856194558) (.leaf 836837338)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 817970498) (.leaf 799579157)) (.branch 70 (.leaf 781648992) (.leaf 764166212))) (.branch 73 (.branch 72 (.leaf 747117538) (.leaf 730490179)) (.branch 74 (.leaf 714271807) (.leaf 698450543))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 683014929) (.branch 77 (.leaf 667953918) (.leaf 653256852))) (.branch 80 (.branch 79 (.leaf 638913445) (.leaf 624913769)) (.branch 81 (.leaf 611248237) (.leaf 597907591)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 584882887) (.leaf 572165482)) (.branch 85 (.leaf 559747020) (.leaf 547619425))) (.branch 88 (.branch 87 (.leaf 535774883) (.leaf 524205838)) (.branch 89 (.leaf 512904977) (.leaf 501865224)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 491079726) (.branch 92 (.leaf 480541850) (.leaf 470245169))) (.branch 95 (.branch 94 (.leaf 460183459) (.leaf 450350686)) (.branch 96 (.leaf 440741003) (.leaf 431348743)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 422168407) (.leaf 413194665)) (.branch 100 (.leaf 404422345) (.leaf 395846428))) (.branch 103 (.branch 102 (.leaf 387462043) (.leaf 379264463)) (.branch 104 (.leaf 371249096) (.leaf 363411484))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355747297) (.leaf 348252328)) (.branch 108 (.leaf 340922490) (.leaf 333753808))) (.branch 111 (.branch 110 (.leaf 326742422) (.leaf 319884577)) (.branch 112 (.leaf 313176621) (.leaf 306615004)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300196271) (.leaf 293917063)) (.branch 116 (.leaf 287774109) (.leaf 281764227))) (.branch 119 (.branch 118 (.leaf 275884319) (.leaf 270131370)) (.branch 120 (.leaf 264502444) (.leaf 258994681)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 697).q*(generalMeanRows 697).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 697).q*(generalMeanRows 697).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5139624639) (.branch 2 (.leaf 4970174667) (.leaf 4808159314))) (.branch 5 (.branch 4 (.leaf 4653158583) (.leaf 4504782035)) (.branch 6 (.leaf 4362666215) (.leaf 4226472343)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4095884256) (.leaf 3970606559)) (.branch 10 (.leaf 3850362962) (.leaf 3734894779))) (.branch 13 (.branch 12 (.leaf 3623959571) (.leaf 3517329916)) (.branch 14 (.leaf 3414792294) (.leaf 3316146067))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3221202554) (.branch 17 (.leaf 3129784181) (.leaf 3041723709))) (.branch 20 (.branch 19 (.leaf 2956863518) (.leaf 2875054958)) (.branch 21 (.leaf 2796157746) (.leaf 2720039413)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646574795) (.leaf 2575645557)) (.branch 25 (.leaf 2507139766) (.leaf 2440951477))) (.branch 28 (.branch 27 (.leaf 2376980367) (.leaf 2315131384)) (.branch 29 (.leaf 2255314429) (.leaf 2197444050)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2141439170) (.branch 32 (.leaf 2087222823) (.leaf 2034721913))) (.branch 35 (.branch 34 (.leaf 1983866993) (.leaf 1934592046)) (.branch 36 (.leaf 1886834294) (.leaf 1840534014)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1795634363) (.leaf 1752081220)) (.branch 40 (.leaf 1709823031) (.leaf 1668810673))) (.branch 43 (.branch 42 (.leaf 1628997315) (.leaf 1590338300)) (.branch 44 (.leaf 1552791021) (.leaf 1516314819))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1480870873) (.branch 47 (.leaf 1446422106) (.leaf 1412933094))) (.branch 50 (.branch 49 (.leaf 1380369979) (.leaf 1348700389)) (.branch 51 (.leaf 1317893358) (.leaf 1287919262)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1258749742) (.leaf 1230357649)) (.branch 55 (.leaf 1202716974) (.leaf 1175802802))) (.branch 58 (.branch 57 (.leaf 1149591247) (.leaf 1124059411)) (.branch 59 (.leaf 1099185330) (.leaf 1074947930))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1051326987) (.branch 62 (.leaf 1028303080) (.leaf 1005857561))) (.branch 65 (.branch 64 (.leaf 983972511) (.leaf 962630711)) (.branch 66 (.leaf 941815606) (.leaf 921511277)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 901702408) (.leaf 882374263)) (.branch 70 (.leaf 863512656) (.leaf 845103928))) (.branch 73 (.branch 72 (.leaf 827134923) (.leaf 809592963)) (.branch 74 (.leaf 792465831) (.leaf 775741751))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 759409361) (.branch 77 (.leaf 743457706) (.leaf 727876211))) (.branch 80 (.branch 79 (.leaf 712654672) (.leaf 697783233)) (.branch 81 (.leaf 683252378) (.leaf 669052914)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 655175955) (.leaf 641612914)) (.branch 85 (.leaf 628355486) (.leaf 615395641))) (.branch 88 (.branch 87 (.leaf 602725609) (.leaf 590337872)) (.branch 89 (.leaf 578225153) (.leaf 566380406)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 554796808) (.branch 92 (.leaf 543467749) (.leaf 532386824))) (.branch 95 (.branch 94 (.leaf 521547827) (.leaf 510944739)) (.branch 96 (.leaf 500571727) (.leaf 490423131)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 480493462) (.leaf 470777392)) (.branch 100 (.leaf 461269752) (.leaf 451965521))) (.branch 103 (.branch 102 (.leaf 442859827) (.leaf 433947935)) (.branch 104 (.leaf 425225249) (.leaf 416687300))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408329746) (.leaf 400148368)) (.branch 108 (.leaf 392139062) (.leaf 384297838))) (.branch 111 (.branch 110 (.leaf 376620816) (.leaf 369104221)) (.branch 112 (.leaf 361744379) (.leaf 354537717)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 347480756) (.leaf 340570108)) (.branch 116 (.leaf 333802477) (.leaf 327174650))) (.branch 119 (.branch 118 (.leaf 320683500) (.leaf 314325981)) (.branch 120 (.leaf 308099123) (.leaf 302000034)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 698).q*(generalMeanRows 698).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 698).q*(generalMeanRows 698).cutoff/2-2 = (15814/7697:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable236.value]
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

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5009022415) (.branch 2 (.leaf 4839224782) (.leaf 4676933293))) (.branch 5 (.branch 4 (.leaf 4521724523) (.leaf 4373204795)) (.branch 6 (.leaf 4231007582) (.leaf 4094791191)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3964236690) (.leaf 3839046051)) (.branch 10 (.leaf 3718940475) (.leaf 3603658884))) (.branch 13 (.branch 12 (.leaf 3492956556) (.leaf 3386603891)) (.branch 14 (.leaf 3284385281) (.leaf 3186098096))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3091551744) (.branch 17 (.leaf 3000566822) (.leaf 2912974337))) (.branch 20 (.branch 19 (.leaf 2828614987) (.leaf 2747338507)) (.branch 21 (.leaf 2669003064) (.leaf 2593474699)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2520626816) (.leaf 2450339706)) (.branch 25 (.leaf 2382500111) (.leaf 2317000815))) (.branch 28 (.branch 27 (.leaf 2253740270) (.leaf 2192622246)) (.branch 29 (.leaf 2133555507) (.leaf 2076453513)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2021234132) (.branch 32 (.leaf 1967819386) (.leaf 1916135207))) (.branch 35 (.branch 34 (.leaf 1866111203) (.leaf 1817680456)) (.branch 36 (.leaf 1770779315) (.leaf 1725347217)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1681326511) (.leaf 1638662295)) (.branch 40 (.leaf 1597302266) (.leaf 1557196576))) (.branch 43 (.branch 42 (.leaf 1518297700) (.leaf 1480560307)) (.branch 44 (.leaf 1443941147) (.leaf 1408398936))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1373894257) (.branch 47 (.leaf 1340389454) (.leaf 1307848550))) (.branch 50 (.branch 49 (.leaf 1276237151) (.leaf 1245522371)) (.branch 51 (.leaf 1215672753) (.leaf 1186658193)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1158449880) (.leaf 1131020220)) (.branch 55 (.leaf 1104342786) (.leaf 1078392255))) (.branch 58 (.branch 57 (.leaf 1053144353) (.leaf 1028575807)) (.branch 59 (.leaf 1004664293) (.leaf 981388394))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 958727554) (.branch 62 (.leaf 936662037) (.leaf 915172890))) (.branch 65 (.branch 64 (.leaf 894241904) (.leaf 873851581)) (.branch 66 (.leaf 853985100) (.leaf 834626286)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 815759582) (.leaf 797370017)) (.branch 70 (.leaf 779443184) (.leaf 761965211))) (.branch 73 (.branch 72 (.leaf 744922741) (.leaf 728302903)) (.branch 74 (.leaf 712093298) (.leaf 696281972))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 680857403) (.branch 77 (.leaf 665808474) (.leaf 651124463))) (.branch 80 (.branch 79 (.leaf 636795023) (.leaf 622810168)) (.branch 81 (.leaf 609160252) (.leaf 595835964)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 582828306) (.leaf 570128585)) (.branch 85 (.leaf 557728397) (.leaf 545619619))) (.branch 88 (.branch 87 (.leaf 533794393) (.leaf 522245121)) (.branch 89 (.leaf 510964450) (.leaf 499945263)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 489180673) (.branch 92 (.leaf 478664009) (.leaf 468388812))) (.branch 95 (.branch 94 (.leaf 458348825) (.leaf 448537984)) (.branch 96 (.leaf 438950413) (.leaf 429580416)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 420422470) (.leaf 411471218)) (.branch 100 (.leaf 402721466) (.leaf 394168172))) (.branch 103 (.branch 102 (.leaf 385806443) (.leaf 377631533)) (.branch 104 (.leaf 369638830) (.leaf 361823860))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 354182275) (.leaf 346709851)) (.branch 108 (.leaf 339402487) (.leaf 332256195))) (.branch 111 (.branch 110 (.leaf 325267100) (.leaf 318431435)) (.branch 112 (.leaf 311745538) (.leaf 305205846)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 298808895) (.leaf 292551317)) (.branch 116 (.leaf 286429831) (.leaf 280441248))) (.branch 119 (.branch 118 (.leaf 274582462) (.leaf 268850451)) (.branch 120 (.leaf 263242272) (.leaf 257755061)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

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
    have hfirst : (generalMeanRows 699).q*(generalMeanRows 699).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 699).q*(generalMeanRows 699).cutoff/2-2 = (15814/7697:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable236.value]
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
