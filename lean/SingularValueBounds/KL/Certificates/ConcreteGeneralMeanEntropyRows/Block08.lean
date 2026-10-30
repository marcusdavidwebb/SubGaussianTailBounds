import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block12
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 560. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0560
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5316957247) (.branch 2 (.leaf 5149355833) (.leaf 4989123736))) (.branch 5 (.branch 4 (.leaf 4835837389) (.leaf 4689103351)) (.branch 6 (.leaf 4548555667) (.leaf 4413853528)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4284679161) (.leaf 4160735948)) (.branch 10 (.leaf 4041746724) (.leaf 3927452243))) (.branch 13 (.branch 12 (.leaf 3817609792) (.leaf 3711991935)) (.branch 14 (.leaf 3610385369) (.leaf 3512589882))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3418417406) (.branch 17 (.leaf 3327691149) (.leaf 3240244802))) (.branch 20 (.branch 19 (.leaf 3155921808) (.leaf 3074574696)) (.branch 21 (.leaf 2996064464) (.leaf 2920260016)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2847037635) (.leaf 2776280504)) (.branch 25 (.leaf 2707878258) (.leaf 2641726574))) (.branch 28 (.branch 27 (.leaf 2577726788) (.leaf 2515785536)) (.branch 29 (.leaf 2455814431) (.leaf 2397729755)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2341452173) (.branch 32 (.leaf 2286906469) (.leaf 2234021301))) (.branch 35 (.branch 34 (.leaf 2182728969) (.leaf 2132965201)) (.branch 36 (.leaf 2084668954) (.leaf 2037782224)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1992249874) (.leaf 1948019470)) (.branch 40 (.leaf 1905041124) (.leaf 1863267357))) (.branch 43 (.branch 42 (.leaf 1822652959) (.leaf 1783154865)) (.branch 44 (.leaf 1744732038) (.leaf 1707345354))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1670957504) (.branch 47 (.leaf 1635532891) (.leaf 1601037539))) (.branch 50 (.branch 49 (.leaf 1567439008) (.leaf 1534706311)) (.branch 51 (.leaf 1502809840) (.leaf 1471721291)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1441413595) (.leaf 1411860860)) (.branch 55 (.leaf 1383038305) (.leaf 1354922205))) (.branch 58 (.branch 57 (.leaf 1327489839) (.leaf 1300719436)) (.branch 59 (.leaf 1274590131) (.leaf 1249081918))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1224175606) (.branch 62 (.leaf 1199852783) (.leaf 1176095774))) (.branch 65 (.branch 64 (.leaf 1152887607) (.leaf 1130211979)) (.branch 66 (.leaf 1108053225) (.leaf 1086396283)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1065226671) (.leaf 1044530457)) (.branch 70 (.leaf 1024294235) (.leaf 1004505096))) (.branch 73 (.branch 72 (.leaf 985150612) (.leaf 966218806)) (.branch 74 (.leaf 947698141) (.leaf 929577490))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 911846126) (.branch 77 (.leaf 894493697) (.leaf 877510216))) (.branch 80 (.branch 79 (.leaf 860886040) (.leaf 844611859)) (.branch 81 (.leaf 828678676) (.leaf 813077799)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 797800827) (.leaf 782839633)) (.branch 85 (.leaf 768186360) (.leaf 753833403))) (.branch 88 (.branch 87 (.leaf 739773401) (.leaf 725999229)) (.branch 89 (.leaf 712503985) (.leaf 699280984)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 686323745) (.branch 92 (.leaf 673625988) (.leaf 661181623))) (.branch 95 (.branch 94 (.leaf 648984744) (.leaf 637029618)) (.branch 96 (.leaf 625310684) (.leaf 613822543)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 602559953) (.leaf 591517821)) (.branch 100 (.leaf 580691201) (.leaf 570075286))) (.branch 103 (.branch 102 (.leaf 559665402) (.leaf 549457006)) (.branch 104 (.leaf 539445681) (.leaf 529627127))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 519997165) (.leaf 510551723)) (.branch 108 (.leaf 501286840) (.leaf 492198660))) (.branch 111 (.branch 110 (.leaf 483283426) (.leaf 474537479)) (.branch 112 (.leaf 465957254) (.leaf 457539278)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449280165) (.leaf 441176615)) (.branch 116 (.leaf 433225408) (.leaf 425423407))) (.branch 119 (.branch 118 (.leaf 417767550) (.leaf 410254849)) (.branch 120 (.leaf 402882392) (.leaf 395647332)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 560).prefactor = (574684715403257/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 560).cutoff/(generalMeanRows 560).c)).2 =
    (421595503595919/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 560).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 560).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 560).q*(generalMeanRows 560).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    have hcontinuation : (generalMeanRows 560).q*(generalMeanRows 560).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 560).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 560

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 560).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 560).criticalRate j.val*(generalMeanRows 560).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 560).c*(generalMeanRows 560).criticalPoint j.val)).2-
      (generalMeanRows 560).J/2-(generalMeanRows 560).error (generalMeanGrid j.val)+
      (generalMeanRows 560).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 560).c)).2-
      (generalMeanRows 560).J/2-(generalMeanRows 560).error 4 := by
  have he : (generalMeanRows 560).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 560) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 560)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0560

/-! Kernel-checked entropy margins for general spectral rectangle 561. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0561
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5244887566) (.branch 2 (.leaf 5076998470) (.leaf 4916514477))) (.branch 5 (.branch 4 (.leaf 4763010503) (.leaf 4616091668)) (.branch 6 (.leaf 4475390652) (.leaf 4340565344)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4211296738) (.leaf 4087287034)) (.branch 10 (.leaf 3968257938) (.leaf 3853949130))) (.branch 13 (.branch 12 (.leaf 3744116865) (.leaf 3638532717)) (.branch 14 (.leaf 3536982436) (.leaf 3439264901))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3345191168) (.branch 17 (.leaf 3254583605) (.leaf 3167275093))) (.branch 20 (.branch 19 (.leaf 3083108296) (.leaf 3001934992)) (.branch 21 (.leaf 2923615456) (.leaf 2848017891)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2775017908) (.leaf 2704498038)) (.branch 25 (.leaf 2636347289) (.leaf 2570460729))) (.branch 28 (.branch 27 (.leaf 2506739106) (.leaf 2445088491)) (.branch 29 (.leaf 2385419946) (.leaf 2327649221)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2271696469) (.branch 32 (.leaf 2217485975) (.leaf 2164945916))) (.branch 35 (.branch 34 (.leaf 2114008126) (.leaf 2064607881)) (.branch 36 (.leaf 2016683701) (.leaf 1970177160)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1925032709) (.leaf 1881197517)) (.branch 40 (.leaf 1838621313) (.leaf 1797256244))) (.branch 43 (.branch 42 (.leaf 1757056739) (.leaf 1717979384)) (.branch 44 (.leaf 1679982803) (.leaf 1643027545))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1607075981) (.branch 47 (.leaf 1572092209) (.leaf 1538041953))) (.branch 50 (.branch 49 (.leaf 1504892485) (.leaf 1472612539)) (.branch 51 (.leaf 1441172236) (.leaf 1410543009)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1380697538) (.leaf 1351609683)) (.branch 55 (.leaf 1323254427) (.leaf 1295607816))) (.branch 58 (.branch 57 (.leaf 1268646904) (.leaf 1242349707)) (.branch 59 (.leaf 1216695151) (.leaf 1191663029))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1167233957) (.branch 62 (.leaf 1143389333) (.leaf 1120111302))) (.branch 65 (.branch 64 (.leaf 1097382716) (.leaf 1075187103)) (.branch 66 (.leaf 1053508632) (.leaf 1032332086)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1011642830) (.leaf 991426785)) (.branch 70 (.leaf 971670401) (.leaf 952360634))) (.branch 73 (.branch 72 (.leaf 933484923) (.leaf 915031167)) (.branch 74 (.leaf 896987702) (.leaf 879343287))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 862087079) (.branch 77 (.leaf 845208618) (.leaf 828697813))) (.branch 80 (.branch 79 (.leaf 812544918) (.leaf 796740526)) (.branch 81 (.leaf 781275550) (.leaf 766141206)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 751329007) (.leaf 736830745)) (.branch 85 (.leaf 722638484) (.leaf 708744543))) (.branch 88 (.branch 87 (.leaf 695141490) (.leaf 681822129)) (.branch 89 (.leaf 668779495) (.leaf 656006836)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 643497614) (.branch 92 (.leaf 631245492) (.leaf 619244323))) (.branch 95 (.branch 94 (.leaf 607488150) (.leaf 595971191)) (.branch 96 (.leaf 584687839) (.leaf 573632650)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 562800339) (.leaf 552185774)) (.branch 100 (.leaf 541783972) (.leaf 531590089))) (.branch 103 (.branch 102 (.leaf 521599420) (.leaf 511807389)) (.branch 104 (.leaf 502209550) (.leaf 492801577))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 483579262) (.leaf 474538513)) (.branch 108 (.leaf 465675346) (.leaf 456985884))) (.branch 111 (.branch 110 (.leaf 448466350) (.leaf 440113071)) (.branch 112 (.leaf 431922465) (.leaf 423891044)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 416015410) (.leaf 408292252)) (.branch 116 (.leaf 400718340) (.leaf 393290528))) (.branch 119 (.branch 118 (.leaf 386005747) (.leaf 378861004)) (.branch 120 (.leaf 371853379) (.leaf 364980024)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 561).prefactor = (4613228629972819/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 561).cutoff/(generalMeanRows 561).c)).2 =
    (413843526791601/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 561).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 561).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 561).q*(generalMeanRows 561).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 561).q*(generalMeanRows 561).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 561).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 561

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 561).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 561).criticalRate j.val*(generalMeanRows 561).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 561).c*(generalMeanRows 561).criticalPoint j.val)).2-
      (generalMeanRows 561).J/2-(generalMeanRows 561).error (generalMeanGrid j.val)+
      (generalMeanRows 561).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 561).c)).2-
      (generalMeanRows 561).J/2-(generalMeanRows 561).error 4 := by
  have he : (generalMeanRows 561).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 561) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 561)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0561

/-! Kernel-checked entropy margins for general spectral rectangle 562. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0562
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5264116453) (.branch 2 (.leaf 5095620418) (.leaf 4934542672))) (.branch 5 (.branch 4 (.leaf 4780458358) (.leaf 4632972760)) (.branch 6 (.leaf 4491718678) (.leaf 4356354069)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4226559951) (.leaf 4102038513)) (.branch 10 (.leaf 3982511414) (.leaf 3867718252))) (.branch 13 (.branch 12 (.leaf 3757415175) (.leaf 3651373627)) (.branch 14 (.leaf 3549379201) (.leaf 3451230602))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3356738696) (.branch 17 (.leaf 3265725644) (.leaf 3178024107))) (.branch 20 (.branch 19 (.leaf 3093476521) (.leaf 3011934424)) (.branch 21 (.leaf 2933257844) (.leaf 2857314732)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2783980440) (.leaf 2713137237)) (.branch 25 (.leaf 2644673868) (.leaf 2578485135))) (.branch 28 (.branch 27 (.leaf 2514471519) (.leaf 2452538822)) (.branch 29 (.leaf 2392597844) (.leaf 2334564068)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2278357383) (.branch 32 (.leaf 2223901817) (.leaf 2171125287))) (.branch 35 (.branch 34 (.leaf 2119959374) (.leaf 2070339104)) (.branch 36 (.leaf 2022202748) (.leaf 1975491639)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1930149992) (.leaf 1886124740)) (.branch 40 (.leaf 1843365384) (.leaf 1801823848))) (.branch 43 (.branch 42 (.leaf 1761454342) (.leaf 1722213238)) (.branch 44 (.leaf 1684058951) (.leaf 1646951828))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1610854041) (.branch 47 (.leaf 1575729494) (.leaf 1541543724))) (.branch 50 (.branch 49 (.leaf 1508263821) (.leaf 1475858342)) (.branch 51 (.leaf 1444297232) (.leaf 1413551760)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1383594442) (.leaf 1354398981)) (.branch 55 (.leaf 1325940206) (.leaf 1298194015))) (.branch 58 (.branch 57 (.leaf 1271137319) (.leaf 1244747996)) (.branch 59 (.leaf 1219004836) (.leaf 1193887503))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1169376485) (.branch 62 (.leaf 1145453062) (.leaf 1122099258))) (.branch 65 (.branch 64 (.leaf 1099297812) (.leaf 1077032144)) (.branch 66 (.leaf 1055286316) (.leaf 1034045008)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1013293487) (.leaf 993017578)) (.branch 70 (.leaf 973203640) (.leaf 953838540))) (.branch 73 (.branch 72 (.leaf 934909632) (.leaf 916404732)) (.branch 74 (.leaf 898312097) (.leaf 880620408))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 863318751) (.branch 77 (.leaf 846396594) (.leaf 829843775))) (.branch 80 (.branch 79 (.leaf 813650487) (.leaf 797807257)) (.branch 81 (.leaf 782304935) (.leaf 767134683)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 752287954) (.leaf 737756488)) (.branch 85 (.leaf 723532295) (.leaf 709607644))) (.branch 88 (.branch 87 (.leaf 695975055) (.leaf 682627287)) (.branch 89 (.leaf 669557328) (.leaf 656758385)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 644223877) (.branch 92 (.leaf 631947428) (.leaf 619922855))) (.branch 95 (.branch 94 (.leaf 608144161) (.leaf 596605532)) (.branch 96 (.leaf 585301325) (.leaf 574226064)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 563374434) (.leaf 552741272)) (.branch 100 (.leaf 542321567) (.leaf 532110446))) (.branch 103 (.branch 102 (.leaf 522103179) (.leaf 512295165)) (.branch 104 (.leaf 502681932) (.leaf 493259131))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 484022532) (.leaf 474968022)) (.branch 108 (.leaf 466091595) (.leaf 457389354))) (.branch 111 (.branch 110 (.leaf 448857505) (.leaf 440492354)) (.branch 112 (.leaf 432290303) (.leaf 424247848)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 416361573) (.leaf 408628152)) (.branch 116 (.leaf 401044342) (.leaf 393606980))) (.branch 119 (.branch 118 (.leaf 386312984) (.leaf 379159348)) (.branch 120 (.leaf 372143141) (.leaf 365261501)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 562).prefactor = (576936448928419/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 562).cutoff/(generalMeanRows 562).c)).2 =
    (41098229451057/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 562).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 562).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 562).q*(generalMeanRows 562).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 562).q*(generalMeanRows 562).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 562).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 562

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 562).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 562).criticalRate j.val*(generalMeanRows 562).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 562).c*(generalMeanRows 562).criticalPoint j.val)).2-
      (generalMeanRows 562).J/2-(generalMeanRows 562).error (generalMeanGrid j.val)+
      (generalMeanRows 562).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 562).c)).2-
      (generalMeanRows 562).J/2-(generalMeanRows 562).error 4 := by
  have he : (generalMeanRows 562).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 562) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 562)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0562

/-! Kernel-checked entropy margins for general spectral rectangle 563. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0563
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5193561456) (.branch 2 (.leaf 5024811455) (.leaf 4863515547))) (.branch 5 (.branch 4 (.leaf 4709247305) (.leaf 4561610529)) (.branch 6 (.leaf 4420236607) (.leaf 4284782158)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4154926923) (.leaf 4030371874)) (.branch 10 (.leaf 3910837512) (.leaf 3796062324))) (.branch 13 (.branch 12 (.leaf 3685801399) (.leaf 3579825165)) (.branch 14 (.leaf 3477918241) (.leaf 3379878399))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3285515609) (.branch 17 (.leaf 3194651170) (.leaf 3107116916))) (.branch 20 (.branch 19 (.leaf 3022754486) (.leaf 2941414650)) (.branch 21 (.leaf 2862956699) (.leaf 2787247872)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2714162835) (.leaf 2643583195)) (.branch 25 (.leaf 2575397057) (.leaf 2509498608))) (.branch 28 (.branch 27 (.leaf 2445787734) (.leaf 2384169663)) (.branch 29 (.leaf 2324554637) (.leaf 2266857605)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2210997938) (.branch 32 (.leaf 2156899160) (.leaf 2104488706))) (.branch 35 (.branch 34 (.leaf 2053697687) (.leaf 2004460676)) (.branch 36 (.leaf 1956715507) (.leaf 1910403089)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1865467224) (.leaf 1821854453)) (.branch 40 (.leaf 1779513890) (.leaf 1738397090))) (.branch 43 (.branch 42 (.leaf 1698457902) (.leaf 1659652353)) (.branch 44 (.leaf 1621938521) (.leaf 1585276427))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1549627932) (.branch 47 (.leaf 1514956633) (.leaf 1481227776))) (.branch 50 (.branch 49 (.leaf 1448408164) (.leaf 1416466080)) (.branch 51 (.leaf 1385371206) (.leaf 1355094551)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1325608385) (.leaf 1296886170)) (.branch 55 (.leaf 1268902504) (.leaf 1241633061))) (.branch 58 (.branch 57 (.leaf 1215054536) (.leaf 1189144599)) (.branch 59 (.leaf 1163881838) (.leaf 1139245721))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1115216552) (.branch 62 (.leaf 1091775427) (.leaf 1068904196))) (.branch 65 (.branch 64 (.leaf 1046585432) (.leaf 1024802389)) (.branch 66 (.leaf 1003538975) (.leaf 982779719)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 962509743) (.leaf 942714731)) (.branch 70 (.leaf 923380910) (.leaf 904495017))) (.branch 73 (.branch 72 (.leaf 886044280) (.leaf 868016396)) (.branch 74 (.leaf 850399509) (.leaf 833182189))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 816353415) (.branch 77 (.leaf 799902554) (.leaf 783819348))) (.branch 80 (.branch 79 (.leaf 768093895) (.leaf 752716633)) (.branch 81 (.leaf 737678327) (.leaf 722970056)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 708583196) (.leaf 694509412)) (.branch 85 (.leaf 680740642) (.leaf 667269088))) (.branch 88 (.branch 87 (.leaf 654087205) (.leaf 641187689)) (.branch 89 (.leaf 628563470) (.leaf 616207700)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 604113746) (.branch 92 (.leaf 592275179) (.leaf 580685769))) (.branch 95 (.branch 94 (.leaf 569339476) (.leaf 558230442)) (.branch 96 (.leaf 547352984) (.leaf 536701590)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 526270908) (.leaf 516055743)) (.branch 100 (.leaf 506051052) (.leaf 496251935))) (.branch 103 (.branch 102 (.leaf 486653633) (.leaf 477251520)) (.branch 104 (.leaf 468041103) (.leaf 459018011))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 450177996) (.leaf 441516923)) (.branch 108 (.leaf 433030774) (.leaf 424715637))) (.branch 111 (.branch 110 (.leaf 416567704) (.leaf 408583271)) (.branch 112 (.leaf 400758729) (.leaf 393090565)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 385575358) (.leaf 378209775)) (.branch 116 (.leaf 370990567) (.leaf 363914570))) (.branch 119 (.branch 118 (.leaf 356978698) (.leaf 350179946)) (.branch 120 (.leaf 343515381) (.leaf 336982144)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 563).prefactor = (2315717265347287/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 563).cutoff/(generalMeanRows 563).c)).2 =
    (80657989777483/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 563).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 563).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 563).q*(generalMeanRows 563).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 563).q*(generalMeanRows 563).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 563).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 563

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 563).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 563).criticalRate j.val*(generalMeanRows 563).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 563).c*(generalMeanRows 563).criticalPoint j.val)).2-
      (generalMeanRows 563).J/2-(generalMeanRows 563).error (generalMeanGrid j.val)+
      (generalMeanRows 563).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 563).c)).2-
      (generalMeanRows 563).J/2-(generalMeanRows 563).error 4 := by
  have he : (generalMeanRows 563).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 563) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 563)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0563

/-! Kernel-checked entropy margins for general spectral rectangle 564. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0564
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5060300749) (.branch 2 (.leaf 4891104859) (.leaf 4729408284))) (.branch 5 (.branch 4 (.leaf 4574784747) (.leaf 4426838049)) (.branch 6 (.leaf 4285199446) (.leaf 4149525305)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4019495007) (.leaf 3894809067)) (.branch 10 (.leaf 3775187441) (.leaf 3660367994))) (.branch 13 (.branch 12 (.leaf 3550105125) (.leaf 3444168511)) (.branch 14 (.leaf 3342341970) (.leaf 3244422422))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3150218949) (.branch 17 (.leaf 3059551928) (.leaf 2972252244))) (.branch 20 (.branch 19 (.leaf 2888160559) (.leaf 2807126654)) (.branch 21 (.leaf 2729008809) (.leaf 2653673246)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2580993606) (.leaf 2510850466)) (.branch 25 (.leaf 2443130900) (.leaf 2377728063))) (.branch 28 (.branch 27 (.leaf 2314540815) (.leaf 2253473362)) (.branch 29 (.leaf 2194434934) (.leaf 2137339475)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2082105360) (.branch 32 (.leaf 2028655134) (.leaf 1976915262))) (.branch 35 (.branch 34 (.leaf 1926815901) (.leaf 1878290685)) (.branch 36 (.leaf 1831276526) (.leaf 1785713425)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1741544299) (.leaf 1698714814)) (.branch 40 (.leaf 1657173235) (.leaf 1616870281))) (.branch 43 (.branch 42 (.leaf 1577758989) (.leaf 1539794587)) (.branch 44 (.leaf 1502934378) (.leaf 1467137628))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1432365456) (.branch 47 (.leaf 1398580745) (.leaf 1365748039))) (.branch 50 (.branch 49 (.leaf 1333833463) (.leaf 1302804639)) (.branch 51 (.leaf 1272630607) (.leaf 1243281755)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1214729746) (.leaf 1186947458)) (.branch 55 (.leaf 1159908922) (.leaf 1133589261))) (.branch 58 (.branch 57 (.leaf 1107964639) (.leaf 1083012209)) (.branch 59 (.leaf 1058710063) (.leaf 1035037189))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1011973424) (.branch 62 (.leaf 989499416) (.leaf 967596583))) (.branch 65 (.branch 64 (.leaf 946247080) (.leaf 925433759)) (.branch 66 (.leaf 905140140) (.leaf 885350380)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 866049241) (.leaf 847222062)) (.branch 70 (.leaf 828854738) (.leaf 810933687))) (.branch 73 (.branch 72 (.leaf 793445831) (.leaf 776378575)) (.branch 74 (.leaf 759719780) (.leaf 743457746))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 727581194) (.branch 77 (.leaf 712079246) (.leaf 696941405))) (.branch 80 (.branch 79 (.leaf 682157544) (.leaf 667717886)) (.branch 81 (.leaf 653612991) (.leaf 639833741)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 626371327) (.leaf 613217234)) (.branch 85 (.leaf 600363234) (.leaf 587801367))) (.branch 88 (.branch 87 (.leaf 575523938) (.leaf 563523498)) (.branch 89 (.leaf 551792841) (.leaf 540324991)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 529113194) (.branch 92 (.leaf 518150906) (.leaf 507431791))) (.branch 95 (.branch 94 (.leaf 496949707) (.leaf 486698703)) (.branch 96 (.leaf 476673008) (.leaf 466867025)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 457275328) (.leaf 447892652)) (.branch 100 (.leaf 438713886) (.leaf 429734071))) (.branch 103 (.branch 102 (.leaf 420948393) (.leaf 412352176)) (.branch 104 (.leaf 403940880) (.leaf 395710093))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 387655530) (.leaf 379773024)) (.branch 108 (.leaf 372058527) (.leaf 364508102))) (.branch 111 (.branch 110 (.leaf 357117921) (.leaf 349884261)) (.branch 112 (.leaf 342803500) (.leaf 335872114)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 329086674) (.leaf 322443841)) (.branch 116 (.leaf 315940366) (.leaf 309573086))) (.branch 119 (.branch 118 (.leaf 303338919) (.leaf 297234865)) (.branch 120 (.leaf 291258001) (.leaf 285405478)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 564).prefactor = (1159058056089423/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 564).cutoff/(generalMeanRows 564).c)).2 =
    (93355104763/244140625000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 564).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 564).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 564).q*(generalMeanRows 564).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 564).q*(generalMeanRows 564).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 564).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 564

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 564).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 564).criticalRate j.val*(generalMeanRows 564).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 564).c*(generalMeanRows 564).criticalPoint j.val)).2-
      (generalMeanRows 564).J/2-(generalMeanRows 564).error (generalMeanGrid j.val)+
      (generalMeanRows 564).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 564).c)).2-
      (generalMeanRows 564).J/2-(generalMeanRows 564).error 4 := by
  have he : (generalMeanRows 564).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 564) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 564)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0564

/-! Kernel-checked entropy margins for general spectral rectangle 565. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0565
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5126056862) (.branch 2 (.leaf 4957063571) (.leaf 4795547328))) (.branch 5 (.branch 4 (.leaf 4641081793) (.leaf 4493270779)) (.branch 6 (.leaf 4351745617) (.leaf 4216162808)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4086201922) (.leaf 3961563708)) (.branch 10 (.leaf 3841968399) (.leaf 3727154176))) (.branch 13 (.branch 12 (.leaf 3616875788) (.leaf 3510903288)) (.branch 14 (.leaf 3409020898) (.leaf 3311025966))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3216728018) (.branch 17 (.leaf 3125947894) (.leaf 3038516952))) (.branch 20 (.branch 19 (.leaf 2954276342) (.leaf 2873076339)) (.branch 21 (.leaf 2794775727) (.leaf 2719241235)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646347013) (.leaf 2575974153)) (.branch 25 (.leaf 2508010241) (.leaf 2442348945))) (.branch 28 (.branch 27 (.leaf 2378889634) (.leaf 2317537023)) (.branch 29 (.leaf 2258200843) (.leaf 2200795538)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2145239977) (.branch 32 (.leaf 2091457190) (.leaf 2039374123))) (.branch 35 (.branch 34 (.leaf 1988921405) (.leaf 1940033136)) (.branch 36 (.leaf 1892646684) (.leaf 1846702500)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1802143938) (.leaf 1758917097)) (.branch 40 (.leaf 1716970663) (.leaf 1676255765))) (.branch 43 (.branch 42 (.leaf 1636725843) (.leaf 1598336520)) (.branch 44 (.leaf 1561045480) (.leaf 1524812363))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1489598652) (.branch 47 (.leaf 1455367584) (.leaf 1422084047))) (.branch 50 (.branch 49 (.leaf 1389714501) (.leaf 1358226893)) (.branch 51 (.leaf 1327590579) (.leaf 1297776251)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1268755872) (.leaf 1240502607)) (.branch 55 (.leaf 1212990765) (.leaf 1186195738))) (.branch 58 (.branch 57 (.leaf 1160093953) (.leaf 1134662813)) (.branch 59 (.leaf 1109880656) (.leaf 1085726704))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1062181022) (.branch 62 (.leaf 1039224477) (.leaf 1016838699))) (.branch 65 (.branch 64 (.leaf 995006045) (.leaf 973709565)) (.branch 66 (.leaf 952932968) (.leaf 932660592)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 912877373) (.leaf 893568820)) (.branch 70 (.leaf 874720987) (.leaf 856320448))) (.branch 73 (.branch 72 (.leaf 838354274) (.leaf 820810011)) (.branch 74 (.leaf 803675656) (.leaf 786939640))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 770590809) (.branch 77 (.leaf 754618402) (.leaf 739012039))) (.branch 80 (.branch 79 (.leaf 723761699) (.leaf 708857711)) (.branch 81 (.leaf 694290731) (.leaf 680051736)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 666132005) (.leaf 652523110)) (.branch 85 (.leaf 639216901) (.leaf 626205497))) (.branch 88 (.branch 87 (.leaf 613481271) (.leaf 601036844)) (.branch 89 (.leaf 588865075) (.leaf 576959048)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 565312065) (.branch 92 (.leaf 553917637) (.leaf 542769476))) (.branch 95 (.branch 94 (.leaf 531861489) (.leaf 521187766)) (.branch 96 (.leaf 510742579) (.leaf 500520369)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 490515743) (.leaf 480723469)) (.branch 100 (.leaf 471138466) (.leaf 461755801))) (.branch 103 (.branch 102 (.leaf 452570685) (.leaf 443578464)) (.branch 104 (.leaf 434774618) (.leaf 426154754))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 417714600) (.leaf 409450004)) (.branch 108 (.leaf 401356930) (.leaf 393431450))) (.branch 111 (.branch 110 (.leaf 385669745) (.leaf 378068097)) (.branch 112 (.leaf 370622888) (.leaf 363330598)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 356187799) (.leaf 349191152)) (.branch 116 (.leaf 342337407) (.leaf 335623396))) (.branch 119 (.branch 118 (.leaf 329046035) (.leaf 322602318)) (.branch 120 (.leaf 316289315) (.leaf 310104169)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 565).prefactor = (2316916912202153/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 565).cutoff/(generalMeanRows 565).c)).2 =
    (392803255049937/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 565).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 565).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 565).q*(generalMeanRows 565).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 565).q*(generalMeanRows 565).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 565).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 565

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 565).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 565).criticalRate j.val*(generalMeanRows 565).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 565).c*(generalMeanRows 565).criticalPoint j.val)).2-
      (generalMeanRows 565).J/2-(generalMeanRows 565).error (generalMeanGrid j.val)+
      (generalMeanRows 565).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 565).c)).2-
      (generalMeanRows 565).J/2-(generalMeanRows 565).error 4 := by
  have he : (generalMeanRows 565).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 565) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 565)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0565

/-! Kernel-checked entropy margins for general spectral rectangle 566. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0566
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5143910203) (.branch 2 (.leaf 4974328332) (.leaf 4812249550))) (.branch 5 (.branch 4 (.leaf 4657246034) (.leaf 4508920214)) (.branch 6 (.leaf 4366902140) (.leaf 4230847116)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4100433594) (.leaf 3975361282)) (.branch 10 (.leaf 3855349439) (.leaf 3740135334))) (.branch 13 (.branch 12 (.leaf 3629472862) (.leaf 3523131275)) (.branch 14 (.leaf 3420894043) (.leaf 3322557808))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3227931434) (.branch 17 (.leaf 3136835135) (.leaf 3049099683))) (.branch 20 (.branch 19 (.leaf 2964565674) (.leaf 2883082863)) (.branch 21 (.leaf 2804509541) (.leaf 2728711973)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2655563871) (.leaf 2584945912)) (.branch 25 (.leaf 2516745291) (.leaf 2450855306))) (.branch 28 (.branch 27 (.leaf 2387174975) (.leaf 2325608681)) (.branch 29 (.leaf 2266065842) (.leaf 2208460602)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2152711549) (.branch 32 (.leaf 2098741444) (.leaf 2046476978))) (.branch 35 (.branch 34 (.leaf 1995848541) (.leaf 1946790001)) (.branch 36 (.leaf 1899238509) (.leaf 1853134307)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1808420554) (.leaf 1765043160)) (.branch 40 (.leaf 1722950632) (.leaf 1682093930))) (.branch 43 (.branch 42 (.leaf 1642426331) (.leaf 1603903303)) (.branch 44 (.leaf 1566482384) (.leaf 1530123071))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1494786717) (.branch 47 (.leaf 1460436426) (.leaf 1427036967))) (.branch 50 (.branch 49 (.leaf 1394554683) (.leaf 1362957408)) (.branch 51 (.leaf 1332214392) (.leaf 1302296225)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1273174772) (.leaf 1244823105)) (.branch 55 (.leaf 1217215443) (.leaf 1190327093))) (.branch 58 (.branch 57 (.leaf 1164134398) (.leaf 1138614686)) (.branch 59 (.leaf 1113746216) (.leaf 1089508139))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1065880450) (.branch 62 (.leaf 1042843951) (.leaf 1020380206))) (.branch 65 (.branch 64 (.leaf 998471512) (.leaf 977100860)) (.branch 66 (.leaf 956251901) (.leaf 935908919)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 916056798) (.leaf 896680996)) (.branch 70 (.leaf 877767518) (.leaf 859302893))) (.branch 73 (.branch 72 (.leaf 841274145) (.leaf 823668778)) (.branch 74 (.leaf 806474746) (.leaf 789680441))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 773274669) (.branch 77 (.leaf 757246633) (.leaf 741585915))) (.branch 80 (.branch 79 (.leaf 726282460) (.leaf 711326563)) (.branch 81 (.leaf 696708849) (.leaf 682420261)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 668452050) (.leaf 654795757)) (.branch 85 (.leaf 641443205) (.leaf 628386483))) (.branch 88 (.branch 87 (.leaf 615617940) (.leaf 603130172)) (.branch 89 (.leaf 590916010) (.leaf 578968516)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 567280968) (.branch 92 (.leaf 555846854) (.leaf 544659866))) (.branch 95 (.branch 94 (.leaf 533713888) (.leaf 523002991)) (.branch 96 (.leaf 512521424) (.leaf 502263612)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492224141) (.leaf 482397762)) (.branch 100 (.leaf 472779375) (.leaf 463364032))) (.branch 103 (.branch 102 (.leaf 454146925) (.leaf 445123386)) (.branch 104 (.leaf 436288878) (.leaf 427638991))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 419169441) (.leaf 410876062)) (.branch 108 (.leaf 402754800) (.leaf 394801717))) (.branch 111 (.branch 110 (.leaf 387012979) (.leaf 379384855)) (.branch 112 (.leaf 371913716) (.leaf 364596028)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357428351) (.leaf 350407336)) (.branch 116 (.leaf 343529720) (.leaf 336792326))) (.branch 119 (.branch 118 (.leaf 330192057) (.leaf 323725897)) (.branch 120 (.leaf 317390906) (.leaf 311184219)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 566).prefactor = (116249320537707/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 566).cutoff/(generalMeanRows 566).c)).2 =
    (392803255049937/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 566).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 566).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 566).q*(generalMeanRows 566).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 566).q*(generalMeanRows 566).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 566).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 566

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 566).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 566).criticalRate j.val*(generalMeanRows 566).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 566).c*(generalMeanRows 566).criticalPoint j.val)).2-
      (generalMeanRows 566).J/2-(generalMeanRows 566).error (generalMeanGrid j.val)+
      (generalMeanRows 566).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 566).c)).2-
      (generalMeanRows 566).J/2-(generalMeanRows 566).error 4 := by
  have he : (generalMeanRows 566).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 566) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 566)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0566

/-! Kernel-checked entropy margins for general spectral rectangle 567. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0567
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5078072070) (.branch 2 (.leaf 4908281980) (.leaf 4746017541))) (.branch 5 (.branch 4 (.leaf 4590850980) (.leaf 4442384706)) (.branch 6 (.leaf 4300248681) (.leaf 4164098065)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4033611113) (.leaf 3908487287)) (.branch 10 (.leaf 3788445560) (.leaf 3673222877))) (.branch 13 (.branch 12 (.leaf 3562572775) (.leaf 3456264122)) (.branch 14 (.leaf 3354079974) (.leaf 3255816542))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3161282235) (.branch 17 (.leaf 3070296800) (.leaf 2982690527))) (.branch 20 (.branch 19 (.leaf 2898303520) (.leaf 2816985030)) (.branch 21 (.leaf 2738592843) (.leaf 2662992708)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2590057824) (.leaf 2519668347)) (.branch 25 (.leaf 2451710956) (.leaf 2386078430))) (.branch 28 (.branch 27 (.leaf 2322669274) (.leaf 2261387358)) (.branch 29 (.leaf 2202141593) (.leaf 2144845619)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2089417527) (.branch 32 (.leaf 2035779589) (.leaf 1983858011))) (.branch 35 (.branch 34 (.leaf 1933582705) (.leaf 1884887073)) (.branch 36 (.leaf 1837707804) (.leaf 1791984690)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1747660446) (.leaf 1704680548)) (.branch 40 (.leaf 1662993079) (.leaf 1622548585))) (.branch 43 (.branch 42 (.leaf 1583299937) (.leaf 1545202207)) (.branch 44 (.leaf 1508212549) (.leaf 1472290083))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1437395795) (.branch 47 (.leaf 1403492435) (.leaf 1370544423))) (.branch 50 (.branch 49 (.leaf 1338517767) (.leaf 1307379972)) (.branch 51 (.leaf 1277099972) (.leaf 1247648048)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1218995767) (.leaf 1191115911)) (.branch 55 (.leaf 1163982418) (.leaf 1137570324))) (.branch 58 (.branch 57 (.leaf 1111855711) (.leaf 1086815650)) (.branch 59 (.leaf 1062428158) (.leaf 1038672147))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1015527384) (.branch 62 (.leaf 992974449) (.leaf 970994696))) (.branch 65 (.branch 64 (.leaf 949570215) (.leaf 928683799)) (.branch 66 (.leaf 908318911) (.leaf 888459651)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 869090728) (.leaf 850197430)) (.branch 70 (.leaf 831765601) (.leaf 813781613))) (.branch 73 (.branch 72 (.leaf 796232342) (.leaf 779105147)) (.branch 74 (.leaf 762387847) (.leaf 746068703))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 730136394) (.branch 77 (.leaf 714580004) (.leaf 699389000))) (.branch 80 (.branch 79 (.leaf 684553220) (.leaf 670062851)) (.branch 81 (.leaf 655908421) (.leaf 642080780)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628571086) (.leaf 615370798)) (.branch 85 (.leaf 602471656) (.leaf 589865673))) (.branch 88 (.branch 87 (.leaf 577545126) (.leaf 565502542)) (.branch 89 (.leaf 553730688) (.leaf 542222564)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 530971392) (.branch 92 (.leaf 519970606) (.leaf 509213846))) (.branch 95 (.branch 94 (.leaf 498694950) (.leaf 488407945)) (.branch 96 (.leaf 478347040) (.leaf 468506620)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 458881238) (.leaf 449465611)) (.branch 100 (.leaf 440254610) (.leaf 431243259))) (.branch 103 (.branch 102 (.leaf 422426726) (.leaf 413800320)) (.branch 104 (.leaf 405359484) (.leaf 397099792))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389016941) (.leaf 381106753)) (.branch 108 (.leaf 373365163) (.leaf 365788222))) (.branch 111 (.branch 110 (.leaf 358372087) (.leaf 351113023)) (.branch 112 (.leaf 344007395) (.leaf 337051667)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 330242397) (.leaf 323576235)) (.branch 116 (.leaf 317049920) (.leaf 310660279))) (.branch 119 (.branch 118 (.leaf 304404218) (.leaf 298278727)) (.branch 120 (.leaf 292280873) (.leaf 286407796)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 567).prefactor = (930502851087753/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 567).cutoff/(generalMeanRows 567).c)).2 =
    (93355104763/244140625000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 567).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 567).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 567).q*(generalMeanRows 567).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 567).q*(generalMeanRows 567).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 567).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 567

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 567).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 567).criticalRate j.val*(generalMeanRows 567).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 567).c*(generalMeanRows 567).criticalPoint j.val)).2-
      (generalMeanRows 567).J/2-(generalMeanRows 567).error (generalMeanGrid j.val)+
      (generalMeanRows 567).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 567).c)).2-
      (generalMeanRows 567).J/2-(generalMeanRows 567).error 4 := by
  have he : (generalMeanRows 567).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 567) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 567)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0567

/-! Kernel-checked entropy margins for general spectral rectangle 568. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0568
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5012003850) (.branch 2 (.leaf 4842057621) (.leaf 4679672355))) (.branch 5 (.branch 4 (.leaf 4524418586) (.leaf 4375897121)) (.branch 6 (.leaf 4233736404) (.leaf 4097590153)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3967135255) (.leaf 3842069870)) (.branch 10 (.leaf 3722111729) (.leaf 3606996594))) (.branch 13 (.branch 12 (.leaf 3496476873) (.leaf 3390320353)) (.branch 14 (.leaf 3288309062) (.leaf 3190238220))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3095915292) (.branch 17 (.leaf 3005159120) (.leaf 2917799125))) (.branch 20 (.branch 19 (.leaf 2833674576) (.leaf 2752633926)) (.branch 21 (.leaf 2674534191) (.leaf 2599240385)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2526624993) (.leaf 2456567494)) (.branch 25 (.leaf 2388953907) (.leaf 2323676383))) (.branch 28 (.branch 27 (.leaf 2260632818) (.leaf 2199726498)) (.branch 29 (.leaf 2140865771) (.leaf 2083963737)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2028937964) (.branch 32 (.leaf 1975710220) (.leaf 1924206230))) (.branch 35 (.branch 34 (.leaf 1874355439) (.leaf 1826090799)) (.branch 36 (.leaf 1779348567) (.leaf 1734068117)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1690191764) (.leaf 1647664597)) (.branch 40 (.leaf 1606434327) (.leaf 1566451139))) (.branch 43 (.branch 42 (.leaf 1527667560) (.leaf 1490038329)) (.branch 44 (.leaf 1453520278) (.leaf 1418072220))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1383654842) (.branch 47 (.leaf 1350230608) (.leaf 1317763665))) (.branch 50 (.branch 49 (.leaf 1286219753) (.leaf 1255566124)) (.branch 51 (.leaf 1225771466) (.leaf 1196805825)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1168640539) (.leaf 1141248174)) (.branch 55 (.leaf 1114602458) (.leaf 1088678226))) (.branch 58 (.branch 57 (.leaf 1063451367) (.leaf 1038898767)) (.branch 59 (.leaf 1014998263) (.leaf 991728598))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 969069375) (.branch 62 (.leaf 947001017) (.leaf 925504728))) (.branch 65 (.branch 64 (.leaf 904562454) (.leaf 884156851)) (.branch 66 (.leaf 864271248) (.leaf 844889620)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 825996556) (.leaf 807577230)) (.branch 70 (.leaf 789617374) (.leaf 772103257))) (.branch 73 (.branch 72 (.leaf 755021655) (.leaf 738359831)) (.branch 74 (.leaf 722105516) (.leaf 706246882))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 690772530) (.branch 77 (.leaf 675671463) (.leaf 660933078))) (.branch 80 (.branch 79 (.leaf 646547140) (.leaf 632503774)) (.branch 81 (.leaf 618793444) (.leaf 605406942)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 592335372) (.leaf 579570138)) (.branch 85 (.leaf 567102935) (.leaf 554925730))) (.branch 88 (.branch 87 (.leaf 543030757) (.leaf 531410504)) (.branch 89 (.leaf 520057700) (.leaf 508965313)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 498126531) (.branch 92 (.leaf 487534761) (.leaf 477183617))) (.branch 95 (.branch 94 (.leaf 467066911) (.leaf 457178650)) (.branch 96 (.leaf 447513022) (.leaf 438064395)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 428827306) (.leaf 419796459)) (.branch 100 (.leaf 410966713) (.leaf 402333082))) (.branch 103 (.branch 102 (.leaf 393890726) (.leaf 385634948)) (.branch 104 (.leaf 377561185) (.leaf 369665008))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 361942114) (.leaf 354388322)) (.branch 108 (.leaf 346999570) (.leaf 339771910))) (.branch 111 (.branch 110 (.leaf 332701504) (.leaf 325784621)) (.branch 112 (.leaf 319017633) (.leaf 312397009)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305919316) (.leaf 299581216)) (.branch 116 (.leaf 293379456) (.leaf 287310873))) (.branch 119 (.branch 118 (.leaf 281372388) (.leaf 275561003)) (.branch 120 (.leaf 269873797) (.leaf 264307928)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 568).prefactor = (933770693510063/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 568).cutoff/(generalMeanRows 568).c)).2 =
    (18743183834761/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 568).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 568).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 568).q*(generalMeanRows 568).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 568).q*(generalMeanRows 568).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 568).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 568

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 568).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 568).criticalRate j.val*(generalMeanRows 568).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 568).c*(generalMeanRows 568).criticalPoint j.val)).2-
      (generalMeanRows 568).J/2-(generalMeanRows 568).error (generalMeanGrid j.val)+
      (generalMeanRows 568).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 568).c)).2-
      (generalMeanRows 568).J/2-(generalMeanRows 568).error 4 := by
  have he : (generalMeanRows 568).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 568) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 568)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0568

/-! Kernel-checked entropy margins for general spectral rectangle 569. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0569
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5174236168) (.branch 2 (.leaf 5006097782) (.leaf 4845400056))) (.branch 5 (.branch 4 (.leaf 4691716355) (.leaf 4544650325)) (.branch 6 (.leaf 4403833249) (.leaf 4268921690)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4139595375) (.leaf 4015555299)) (.branch 10 (.leaf 3896522019) (.leaf 3782234114))) (.branch 13 (.branch 12 (.leaf 3672446786) (.leaf 3566930605)) (.branch 14 (.leaf 3465470352) (.leaf 3367863980))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3273921656) (.branch 17 (.leaf 3183464892) (.leaf 3096325748))) (.branch 20 (.branch 19 (.leaf 3012346096) (.leaf 2931376952)) (.branch 21 (.leaf 2853277858) (.leaf 2777916309)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2705167235) (.leaf 2634912509)) (.branch 25 (.leaf 2567040503) (.leaf 2501445674))) (.branch 28 (.branch 27 (.leaf 2438028176) (.leaf 2376693510)) (.branch 29 (.leaf 2317352185) (.leaf 2259919418)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2204314845) (.branch 32 (.leaf 2150462254) (.leaf 2098289338))) (.branch 35 (.branch 34 (.leaf 2047727465) (.leaf 1998711461)) (.branch 36 (.leaf 1951179408) (.leaf 1905072459)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1860334657) (.leaf 1816912776)) (.branch 40 (.leaf 1774756163) (.leaf 1733816595))) (.branch 43 (.branch 42 (.leaf 1694048144) (.leaf 1655407050)) (.branch 44 (.leaf 1617851602) (.leaf 1581342025))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1545840379) (.branch 47 (.leaf 1511310457) (.leaf 1477717691))) (.branch 50 (.branch 49 (.leaf 1445029070) (.leaf 1413213054)) (.branch 51 (.leaf 1382239499) (.leaf 1352079583)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1322705737) (.leaf 1294091585)) (.branch 55 (.leaf 1266211877) (.leaf 1239042435))) (.branch 58 (.branch 57 (.leaf 1212560100) (.leaf 1186742678)) (.branch 59 (.leaf 1161568896) (.leaf 1137018352))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1113071474) (.branch 62 (.leaf 1089709482) (.leaf 1066914344))) (.branch 65 (.branch 64 (.leaf 1044668747) (.leaf 1022956055)) (.branch 66 (.leaf 1001760283) (.leaf 981066062)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 960858613) (.leaf 941123717)) (.branch 70 (.leaf 921847692) (.leaf 903017364))) (.branch 73 (.branch 72 (.leaf 884620048) (.leaf 866643522)) (.branch 74 (.leaf 849076011) (.leaf 831906161))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 815123025) (.branch 77 (.leaf 798716043) (.leaf 782675023))) (.branch 80 (.branch 79 (.leaf 766990130) (.leaf 751651865)) (.branch 81 (.leaf 736651057) (.leaf 721978840)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 707626650) (.leaf 693586204)) (.branch 85 (.leaf 679849494) (.leaf 666408771))) (.branch 88 (.branch 87 (.leaf 653256540) (.leaf 640385543)) (.branch 89 (.leaf 627788754) (.leaf 615459369)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 603390796) (.branch 92 (.leaf 591576646) (.leaf 580010727))) (.branch 95 (.branch 94 (.leaf 568687037) (.leaf 557599751)) (.branch 96 (.leaf 546743222) (.leaf 536111970)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 525700673) (.leaf 515504167)) (.branch 100 (.leaf 505517438) (.leaf 495735613))) (.branch 103 (.branch 102 (.leaf 486153960) (.leaf 476767880)) (.branch 104 (.leaf 467572902) (.leaf 458564680))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 449738987) (.leaf 441091713)) (.branch 108 (.leaf 432618857) (.leaf 424316529))) (.branch 111 (.branch 110 (.leaf 416180941) (.leaf 408208404)) (.branch 112 (.leaf 400395330) (.leaf 392738222)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 385233675) (.leaf 377878370)) (.branch 116 (.leaf 370669076) (.leaf 363602642))) (.branch 119 (.branch 118 (.leaf 356675996) (.leaf 349886145)) (.branch 120 (.leaf 343230169) (.leaf 336705222)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 569).prefactor = (2314516749574091/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 569).cutoff/(generalMeanRows 569).c)).2 =
    (81230236233689/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 569).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 569).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 569).q*(generalMeanRows 569).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 569).q*(generalMeanRows 569).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 569).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 569

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 569).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 569).criticalRate j.val*(generalMeanRows 569).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 569).c*(generalMeanRows 569).criticalPoint j.val)).2-
      (generalMeanRows 569).J/2-(generalMeanRows 569).error (generalMeanGrid j.val)+
      (generalMeanRows 569).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 569).c)).2-
      (generalMeanRows 569).J/2-(generalMeanRows 569).error 4 := by
  have he : (generalMeanRows 569).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 569) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 569)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0569

/-! Kernel-checked entropy margins for general spectral rectangle 570. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0570
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5191963043) (.branch 2 (.leaf 5023248616) (.leaf 4862000342))) (.branch 5 (.branch 4 (.leaf 4707790122) (.leaf 4560220245)) (.branch 6 (.leaf 4418920732) (.leaf 4283546967)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4153777582) (.leaf 4029312546)) (.branch 10 (.leaf 3909871460) (.leaf 3795192005))) (.branch 13 (.branch 12 (.leaf 3685028547) (.leaf 3579150869)) (.branch 14 (.leaf 3477343014) (.leaf 3379402244))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3285138074) (.branch 17 (.leaf 3194371407) (.leaf 3106933725))) (.branch 20 (.branch 19 (.leaf 3022666359) (.leaf 2941419816)) (.branch 21 (.leaf 2863053155) (.leaf 2787433419)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2714435107) (.leaf 2643939689)) (.branch 25 (.leaf 2575835155) (.leaf 2510015598))) (.branch 28 (.branch 27 (.leaf 2446380833) (.leaf 2384836035)) (.branch 29 (.leaf 2325291407) (.leaf 2267661877)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2211866803) (.branch 32 (.leaf 2157829713) (.leaf 2105478054))) (.branch 35 (.branch 34 (.leaf 2054742956) (.leaf 2005559024)) (.branch 36 (.leaf 1957864127) (.leaf 1911599215)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1866708142) (.leaf 1823137499)) (.branch 40 (.leaf 1780836458) (.leaf 1739756631))) (.branch 43 (.branch 42 (.leaf 1699851934) (.leaf 1661078456)) (.branch 44 (.leaf 1623394343) (.leaf 1586759685))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1551136411) (.branch 47 (.leaf 1516488189) (.leaf 1482780335))) (.branch 50 (.branch 49 (.leaf 1449979723) (.leaf 1418054706)) (.branch 51 (.leaf 1386975036) (.leaf 1356711792)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1327237312) (.leaf 1298525128)) (.branch 55 (.leaf 1270549904) (.leaf 1243287380))) (.branch 58 (.branch 57 (.leaf 1216714317) (.leaf 1190808445)) (.branch 59 (.leaf 1165548418) (.leaf 1140913764))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1116884844) (.branch 62 (.leaf 1093442814) (.leaf 1070569581))) (.branch 65 (.branch 64 (.leaf 1048247770) (.leaf 1026460691)) (.branch 66 (.leaf 1005192302) (.leaf 984427183)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 964150504) (.leaf 944347997)) (.branch 70 (.leaf 925005932) (.leaf 906111091))) (.branch 73 (.branch 72 (.leaf 887650746) (.leaf 869612633)) (.branch 74 (.leaf 851984936) (.leaf 834756263))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 817915628) (.branch 77 (.leaf 801452435) (.leaf 785356459))) (.branch 80 (.branch 79 (.leaf 769617829) (.leaf 754227016)) (.branch 81 (.leaf 739174815) (.leaf 724452332)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 710050971) (.leaf 695962423)) (.branch 85 (.leaf 682178650) (.leaf 668691880))) (.branch 88 (.branch 87 (.leaf 655494589) (.leaf 642579496)) (.branch 89 (.leaf 629939551) (.leaf 617567926)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 605458006) (.branch 92 (.leaf 593603381) (.leaf 581997838))) (.branch 95 (.branch 94 (.leaf 570635352) (.leaf 559510082)) (.branch 96 (.leaf 548616359) (.leaf 537948683)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 527501717) (.leaf 517270278)) (.branch 100 (.leaf 507249335) (.leaf 497433997))) (.branch 103 (.branch 102 (.leaf 487819518) (.leaf 478401281)) (.branch 104 (.leaf 469174801) (.leaf 460135717))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 451279788) (.leaf 442602888)) (.branch 108 (.leaf 434101005) (.leaf 425770233))) (.branch 111 (.branch 110 (.leaf 417606772) (.leaf 409606922)) (.branch 112 (.leaf 401767080) (.leaf 394083739)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 386553481) (.leaf 379172977)) (.branch 116 (.leaf 371938984) (.leaf 364848340))) (.branch 119 (.branch 118 (.leaf 357897964) (.leaf 351084851)) (.branch 120 (.leaf 344406072) (.leaf 337858770)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 570).prefactor = (11612231289067/2500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 570).cutoff/(generalMeanRows 570).c)).2 =
    (81230236233689/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 570).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 570).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 570).q*(generalMeanRows 570).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 570).q*(generalMeanRows 570).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 570).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 570

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 570).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 570).criticalRate j.val*(generalMeanRows 570).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 570).c*(generalMeanRows 570).criticalPoint j.val)).2-
      (generalMeanRows 570).J/2-(generalMeanRows 570).error (generalMeanGrid j.val)+
      (generalMeanRows 570).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 570).c)).2-
      (generalMeanRows 570).J/2-(generalMeanRows 570).error 4 := by
  have he : (generalMeanRows 570).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 570) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 570)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0570

/-! Kernel-checked entropy margins for general spectral rectangle 571. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0571
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5124391998) (.branch 2 (.leaf 4955425021) (.leaf 4793947678))) (.branch 5 (.branch 4 (.leaf 4639531940) (.leaf 4491780090)) (.branch 6 (.leaf 4350322074) (.leaf 4214813143)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4084931738) (.leaf 3960377589)) (.branch 10 (.leaf 3840870014) (.leaf 3726146370))) (.branch 13 (.branch 12 (.leaf 3615960667) (.leaf 3510082298)) (.branch 14 (.leaf 3408294893) (.leaf 3310395275))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3216192503) (.branch 17 (.leaf 3125507002) (.leaf 3038169767))) (.branch 20 (.branch 19 (.leaf 2954021628) (.leaf 2872912581)) (.branch 21 (.leaf 2794701169) (.leaf 2719253910)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646444778) (.leaf 2576154714)) (.branch 25 (.leaf 2508271179) (.leaf 2442687738))) (.branch 28 (.branch 27 (.leaf 2379303678) (.leaf 2318023650)) (.branch 29 (.leaf 2258757340) (.leaf 2201419159)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2145927956) (.branch 32 (.leaf 2092206757) (.leaf 2040182510))) (.branch 35 (.branch 34 (.leaf 1989785860) (.leaf 1940950927)) (.branch 36 (.leaf 1893615110) (.leaf 1847718895)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1803205678) (.leaf 1760021605)) (.branch 40 (.leaf 1718115413) (.leaf 1677438286))) (.branch 43 (.branch 42 (.leaf 1637943722) (.leaf 1599587402)) (.branch 44 (.leaf 1562327075) (.leaf 1526122442))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1490935054) (.branch 47 (.leaf 1456728212) (.leaf 1423466872))) (.branch 50 (.branch 49 (.leaf 1391117560) (.leaf 1359648291)) (.branch 51 (.leaf 1329028486) (.leaf 1299228907)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1270221580) (.leaf 1241979736)) (.branch 55 (.leaf 1214477749) (.leaf 1187691075))) (.branch 58 (.branch 57 (.leaf 1161596201) (.leaf 1136170596)) (.branch 59 (.leaf 1111392654) (.leaf 1087241657))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1063697727) (.branch 62 (.leaf 1040741789) (.leaf 1018355527))) (.branch 65 (.branch 64 (.leaf 996521351) (.leaf 975222363)) (.branch 66 (.leaf 954442321) (.leaf 934165613)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 914377223) (.leaf 895062705)) (.branch 70 (.leaf 876208158) (.leaf 857800198))) (.branch 73 (.branch 72 (.leaf 839825938) (.leaf 822272963)) (.branch 74 (.leaf 805129310) (.leaf 788383447))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 772024255) (.branch 77 (.leaf 756041008) (.leaf 740423359))) (.branch 80 (.branch 79 (.leaf 725161319) (.leaf 710245247)) (.branch 81 (.leaf 695665829) (.leaf 681414070)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 667481276) (.leaf 653859044)) (.branch 85 (.leaf 640539250) (.leaf 627514034))) (.branch 88 (.branch 87 (.leaf 614775795) (.leaf 602317174)) (.branch 89 (.leaf 590131050) (.leaf 578210527)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 566548925) (.branch 92 (.leaf 555139774) (.leaf 543976803))) (.branch 95 (.branch 94 (.leaf 533053933) (.leaf 522365272)) (.branch 96 (.leaf 511905104) (.leaf 501667886)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 491648236) (.leaf 481840935)) (.branch 100 (.leaf 472240913) (.leaf 462843251))) (.branch 103 (.branch 102 (.leaf 453643166) (.leaf 444636017)) (.branch 104 (.leaf 435817292) (.leaf 427182606))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418727697) (.leaf 410448419)) (.branch 108 (.leaf 402340744) (.leaf 394400750))) (.branch 111 (.branch 110 (.leaf 386624624) (.leaf 379008655)) (.branch 112 (.leaf 371549230) (.leaf 364242834)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357086042) (.leaf 350075522)) (.branch 116 (.leaf 343208026) (.leaf 336480392))) (.branch 119 (.branch 118 (.leaf 329889536) (.leaf 323432457)) (.branch 120 (.leaf 317106227) (.leaf 310907994)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 571).prefactor = (4647432540436399/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 571).cutoff/(generalMeanRows 571).c)).2 =
    (395656324032343/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 571).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 571).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 571).q*(generalMeanRows 571).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 571).q*(generalMeanRows 571).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 571).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 571

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 571).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 571).criticalRate j.val*(generalMeanRows 571).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 571).c*(generalMeanRows 571).criticalPoint j.val)).2-
      (generalMeanRows 571).J/2-(generalMeanRows 571).error (generalMeanGrid j.val)+
      (generalMeanRows 571).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 571).c)).2-
      (generalMeanRows 571).J/2-(generalMeanRows 571).error 4 := by
  have he : (generalMeanRows 571).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 571) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 571)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0571

/-! Kernel-checked entropy margins for general spectral rectangle 572. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0572
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5056579096) (.branch 2 (.leaf 4887430777) (.leaf 4725807339))) (.branch 5 (.branch 4 (.leaf 4571279117) (.leaf 4423446844)) (.branch 6 (.leaf 4281938999) (.leaf 4146409438)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4016535272) (.leaf 3892014971)) (.branch 10 (.leaf 3772566647) (.leaf 3657926508))) (.branch 13 (.branch 12 (.leaf 3547847464) (.leaf 3442097859)) (.branch 14 (.leaf 3340460318) (.leaf 3242730699))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3148717139) (.branch 17 (.leaf 3058239178) (.leaf 2971126958))) (.branch 20 (.branch 19 (.leaf 2887220496) (.leaf 2806369001)) (.branch 21 (.leaf 2728430260) (.leaf 2653270069)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2580761701) (.leaf 2510785424)) (.branch 25 (.leaf 2443228053) (.leaf 2377982529))) (.branch 28 (.branch 27 (.leaf 2314947537) (.leaf 2254027152)) (.branch 29 (.leaf 2195130497) (.leaf 2138171447)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2083068333) (.branch 32 (.leaf 2029743678) (.leaf 1978123949))) (.branch 35 (.branch 34 (.leaf 1928139323) (.leaf 1879723473)) (.branch 36 (.leaf 1832813363) (.leaf 1787349061)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1743273560) (.leaf 1700532615)) (.branch 40 (.leaf 1659074588) (.leaf 1618850301))) (.branch 43 (.branch 42 (.leaf 1579812902) (.leaf 1541917734)) (.branch 44 (.leaf 1505122222) (.leaf 1469385752))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1434669574) (.branch 47 (.leaf 1400936694) (.leaf 1368151790))) (.branch 50 (.branch 49 (.leaf 1336281115) (.leaf 1305292423)) (.branch 51 (.leaf 1275154884) (.leaf 1245839015)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1217316610) (.leaf 1189560675)) (.branch 55 (.leaf 1162545366) (.leaf 1136245931))) (.branch 58 (.branch 57 (.leaf 1110638658) (.leaf 1085700819)) (.branch 59 (.leaf 1061410626) (.leaf 1037747180))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1014690434) (.branch 62 (.leaf 992221145) (.leaf 970320840))) (.branch 65 (.branch 64 (.leaf 948971777) (.leaf 928156912)) (.branch 66 (.leaf 907859864) (.leaf 888064885)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 868756831) (.leaf 849921135)) (.branch 70 (.leaf 831543774) (.leaf 813611255))) (.branch 73 (.branch 72 (.leaf 796110582) (.leaf 779029237)) (.branch 74 (.leaf 762355157) (.leaf 746076719))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 730182712) (.branch 77 (.leaf 714662326) (.leaf 699505132))) (.branch 80 (.branch 79 (.leaf 684701065) (.leaf 670240408)) (.branch 81 (.leaf 656113780) (.leaf 642312119)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628826668) (.leaf 615648966)) (.branch 85 (.leaf 602770831) (.leaf 590184353))) (.branch 88 (.branch 87 (.leaf 577881879) (.leaf 565856005)) (.branch 89 (.leaf 554099564) (.leaf 542605621)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 531367457) (.branch 92 (.leaf 520378566) (.leaf 509632644))) (.branch 95 (.branch 94 (.leaf 499123582) (.leaf 488845457)) (.branch 96 (.leaf 478792530) (.leaf 468959231)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 459340159) (.leaf 449930073)) (.branch 100 (.leaf 440723887) (.leaf 431716664))) (.branch 103 (.branch 102 (.leaf 422903609) (.leaf 414280067)) (.branch 104 (.leaf 405841517) (.leaf 397583563))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389501937) (.leaf 381592487)) (.branch 108 (.leaf 373851181) (.leaf 366274094))) (.branch 111 (.branch 110 (.leaf 358857412) (.leaf 351597422)) (.branch 112 (.leaf 344490514) (.leaf 337533173)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 330721981) (.leaf 324053608)) (.branch 116 (.leaf 317524812) (.leaf 311132437))) (.branch 119 (.branch 118 (.leaf 304873409) (.leaf 298744735)) (.branch 120 (.leaf 292743495) (.leaf 286866848)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 572).prefactor = (4663485810878553/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 572).cutoff/(generalMeanRows 572).c)).2 =
    (77616106044777/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 572).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 572).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 572).q*(generalMeanRows 572).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 572).q*(generalMeanRows 572).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 572).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 572

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 572).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 572).criticalRate j.val*(generalMeanRows 572).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 572).c*(generalMeanRows 572).criticalPoint j.val)).2-
      (generalMeanRows 572).J/2-(generalMeanRows 572).error (generalMeanGrid j.val)+
      (generalMeanRows 572).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 572).c)).2-
      (generalMeanRows 572).J/2-(generalMeanRows 572).error 4 := by
  have he : (generalMeanRows 572).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 572) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 572)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0572

/-! Kernel-checked entropy margins for general spectral rectangle 573. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0573
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5122462851) (.branch 2 (.leaf 4953535398) (.leaf 4792109513))) (.branch 5 (.branch 4 (.leaf 4637755505) (.leaf 4490074152)) (.branch 6 (.leaf 4348694044) (.leaf 4213269205)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4083476970) (.leaf 3959016077)) (.branch 10 (.leaf 3839604947) (.leaf 3724980139))) (.branch 13 (.branch 12 (.leaf 3614894942) (.leaf 3509118110)) (.branch 14 (.leaf 3407432701) (.leaf 3309635031))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3215533710) (.branch 17 (.leaf 3124948768) (.leaf 3037710851))) (.branch 20 (.branch 19 (.leaf 2953660487) (.leaf 2872647406)) (.branch 21 (.leaf 2794529924) (.leaf 2719174367)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646454542) (.leaf 2576251254)) (.branch 25 (.leaf 2508451850) (.leaf 2442949805))) (.branch 28 (.branch 27 (.leaf 2379644336) (.leaf 2318440041)) (.branch 29 (.leaf 2259246569) (.leaf 2201978308)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2146554100) (.branch 32 (.leaf 2092896971) (.leaf 2040933884))) (.branch 35 (.branch 34 (.leaf 1990595504) (.leaf 1941815983)) (.branch 36 (.leaf 1894532755) (.leaf 1848686349)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1804220212) (.leaf 1761080540)) (.branch 40 (.leaf 1719216127) (.leaf 1678578220))) (.branch 43 (.branch 42 (.leaf 1639120376) (.leaf 1600798345)) (.branch 44 (.leaf 1563569942) (.leaf 1527394936))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1492234947) (.branch 47 (.leaf 1458053346) (.leaf 1424815161))) (.branch 50 (.branch 49 (.leaf 1392486988) (.leaf 1361036912)) (.branch 51 (.leaf 1330434425) (.leaf 1300650357)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1271656804) (.leaf 1243427065)) (.branch 55 (.leaf 1215935581) (.leaf 1189157874))) (.branch 58 (.branch 57 (.leaf 1163070497) (.leaf 1137650979)) (.branch 59 (.leaf 1112877779) (.leaf 1088730240))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1065188543) (.branch 62 (.leaf 1042233668) (.leaf 1019847359))) (.branch 65 (.branch 64 (.leaf 998012078) (.leaf 976710982)) (.branch 66 (.leaf 955927880) (.leaf 935647209)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 915854003) (.leaf 896533862)) (.branch 70 (.leaf 877672930) (.leaf 859257868))) (.branch 73 (.branch 72 (.leaf 841275830) (.leaf 823714443)) (.branch 74 (.leaf 806561782) (.leaf 789806354))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 773437076) (.branch 77 (.leaf 757443257) (.leaf 741814583))) (.branch 80 (.branch 79 (.leaf 726541099) (.leaf 711613193)) (.branch 81 (.leaf 697021581) (.leaf 682757298)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 668811676) (.leaf 655176339)) (.branch 85 (.leaf 641843187) (.leaf 628804385))) (.branch 88 (.branch 87 (.leaf 616052353) (.leaf 603579756)) (.branch 89 (.leaf 591379492) (.leaf 579444685)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 567768675) (.branch 92 (.leaf 556345009) (.leaf 545167432))) (.branch 95 (.branch 94 (.leaf 534229884) (.leaf 523526486)) (.branch 96 (.leaf 513051537) (.leaf 502799507)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492765030) (.leaf 482942897)) (.branch 100 (.leaf 473328050) (.leaf 463915581))) (.branch 103 (.branch 102 (.leaf 454700719) (.leaf 445678830)) (.branch 104 (.leaf 436845413) (.leaf 428196091))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 419726611) (.leaf 411432835)) (.branch 108 (.leaf 403310740) (.leaf 395356412))) (.branch 111 (.branch 110 (.leaf 387566045) (.leaf 379935933)) (.branch 112 (.leaf 372462469) (.leaf 365142141)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357971532) (.leaf 350947311)) (.branch 116 (.leaf 344066236) (.leaf 337325148))) (.branch 119 (.branch 118 (.leaf 330720967) (.leaf 324250693)) (.branch 120 (.leaf 317911403) (.leaf 311700246)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 573).prefactor = (2330402932458367/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 573).cutoff/(generalMeanRows 573).c)).2 =
    (12453673634793/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 573).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 573).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 573).q*(generalMeanRows 573).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 573).q*(generalMeanRows 573).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 573).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 573

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 573).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 573).criticalRate j.val*(generalMeanRows 573).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 573).c*(generalMeanRows 573).criticalPoint j.val)).2-
      (generalMeanRows 573).J/2-(generalMeanRows 573).error (generalMeanGrid j.val)+
      (generalMeanRows 573).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 573).c)).2-
      (generalMeanRows 573).J/2-(generalMeanRows 573).error 4 := by
  have he : (generalMeanRows 573).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 573) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 573)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0573

/-! Kernel-checked entropy margins for general spectral rectangle 574. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0574
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5054326739) (.branch 2 (.leaf 4885222016) (.leaf 4723653978))) (.branch 5 (.branch 4 (.leaf 4569191307) (.leaf 4421433243)) (.branch 6 (.leaf 4280006915) (.leaf 4144564958)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4014783388) (.leaf 3890359685)) (.branch 10 (.leaf 3771011074) (.leaf 3656472966))) (.branch 13 (.branch 12 (.leaf 3546497560) (.leaf 3440852561)) (.branch 14 (.leaf 3339320029) (.leaf 3241695318))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3147786119) (.branch 17 (.leaf 3057411580) (.leaf 2970401499))) (.branch 20 (.branch 19 (.leaf 2886595591) (.leaf 2805842804)) (.branch 21 (.leaf 2728000700) (.leaf 2652934883)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2580518463) (.leaf 2510631573)) (.branch 25 (.leaf 2443160915) (.leaf 2377999343))) (.branch 28 (.branch 27 (.leaf 2315045473) (.leaf 2254203326)) (.branch 29 (.leaf 2195381992) (.leaf 2138495323)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2083461643) (.branch 32 (.leaf 2030203477) (.leaf 1978647307))) (.branch 35 (.branch 34 (.leaf 1928723332) (.leaf 1880365255)) (.branch 36 (.leaf 1833510077) (.leaf 1788097910)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1744071797) (.leaf 1701377545)) (.branch 40 (.leaf 1659963574) (.leaf 1619780766))) (.branch 43 (.branch 42 (.leaf 1580782332) (.leaf 1542923682)) (.branch 44 (.leaf 1506162307) (.leaf 1470457661))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1435771065) (.branch 47 (.leaf 1402065595) (.leaf 1369305998))) (.branch 50 (.branch 49 (.leaf 1337458600) (.leaf 1306491224)) (.branch 51 (.leaf 1276373110) (.leaf 1247074846)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1218568295) (.leaf 1190826529)) (.branch 55 (.leaf 1163823773) (.leaf 1137535341))) (.branch 58 (.branch 57 (.leaf 1111937584) (.leaf 1087007838)) (.branch 59 (.leaf 1062724378) (.leaf 1039066366))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1016013813) (.branch 62 (.leaf 993547534) (.leaf 971649113))) (.branch 65 (.branch 64 (.leaf 950300863) (.leaf 929485791)) (.branch 66 (.leaf 909187569) (.leaf 889390500)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 870079487) (.leaf 851240009)) (.branch 70 (.leaf 832858091) (.leaf 814920282))) (.branch 73 (.branch 72 (.leaf 797413627) (.leaf 780325651)) (.branch 74 (.leaf 763644330) (.leaf 747358077))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 731455720) (.branch 77 (.leaf 715926482) (.leaf 700759968))) (.branch 80 (.branch 79 (.leaf 685946146) (.leaf 671475330)) (.branch 81 (.leaf 657338169) (.leaf 643525628)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 630028978) (.leaf 616839784)) (.branch 85 (.leaf 603949890) (.leaf 591351409))) (.branch 88 (.branch 87 (.leaf 579036710) (.leaf 566998413)) (.branch 89 (.leaf 555229370) (.leaf 543722666)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 532471602) (.branch 92 (.leaf 521469688) (.leaf 510710638))) (.branch 95 (.branch 94 (.leaf 500188360) (.leaf 489896947)) (.branch 96 (.leaf 479830671) (.leaf 469983979)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 460351483) (.leaf 450927954)) (.branch 100 (.leaf 441708317) (.leaf 432687646))) (.branch 103 (.branch 102 (.leaf 423861158) (.leaf 415224207)) (.branch 104 (.leaf 406772281) (.leaf 398500993))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390406083) (.leaf 382483409)) (.branch 108 (.leaf 374728942) (.leaf 367138767))) (.branch 111 (.branch 110 (.leaf 359709074) (.leaf 352436159)) (.branch 112 (.leaf 345316415) (.leaf 338346333)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331522499) (.leaf 324841588)) (.branch 116 (.leaf 318300362) (.leaf 311895670))) (.branch 119 (.branch 118 (.leaf 305624439) (.leaf 299483680)) (.branch 120 (.leaf 293470476) (.leaf 287581989)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 574).prefactor = (2338386866580789/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 574).cutoff/(generalMeanRows 574).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 574).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 574).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 574).q*(generalMeanRows 574).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 574).q*(generalMeanRows 574).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 574).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 574

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 574).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 574).criticalRate j.val*(generalMeanRows 574).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 574).c*(generalMeanRows 574).criticalPoint j.val)).2-
      (generalMeanRows 574).J/2-(generalMeanRows 574).error (generalMeanGrid j.val)+
      (generalMeanRows 574).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 574).c)).2-
      (generalMeanRows 574).J/2-(generalMeanRows 574).error 4 := by
  have he : (generalMeanRows 574).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 574) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 574)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0574

/-! Kernel-checked entropy margins for general spectral rectangle 575. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0575
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5074045650) (.branch 2 (.leaf 4904313055) (.leaf 4742131334))) (.branch 5 (.branch 4 (.leaf 4587069337) (.leaf 4438726418)) (.branch 6 (.leaf 4296729774) (.leaf 4160732062)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4030409283) (.leaf 3905458861)) (.branch 10 (.leaf 3785597935) (.leaf 3670561803))) (.branch 13 (.branch 12 (.leaf 3560102522) (.leaf 3453987634)) (.branch 14 (.leaf 3351999014) (.leaf 3253931816))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3159593512) (.branch 17 (.leaf 3068803019) (.leaf 2981389895))) (.branch 20 (.branch 19 (.leaf 2897193601) (.leaf 2816062826)) (.branch 21 (.leaf 2737854868) (.leaf 2662435057)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2589676228) (.leaf 2519458238)) (.branch 25 (.leaf 2451667509) (.leaf 2386196612))) (.branch 28 (.branch 27 (.leaf 2322943884) (.leaf 2261813065)) (.branch 29 (.leaf 2202712969) (.leaf 2145557169)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2090263717) (.branch 32 (.leaf 2036754866) (.leaf 1984956831))) (.branch 35 (.branch 34 (.leaf 1934799547) (.leaf 1886216458)) (.branch 36 (.leaf 1839144310) (.leaf 1793522964)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1749295216) (.leaf 1706406635)) (.branch 40 (.leaf 1664805402) (.leaf 1624442172))) (.branch 43 (.branch 42 (.leaf 1585269928) (.leaf 1547243863)) (.branch 44 (.leaf 1510321250) (.leaf 1474461339))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1439625243) (.branch 47 (.leaf 1405775843) (.leaf 1372877692))) (.branch 50 (.branch 49 (.leaf 1340896929) (.leaf 1309801195)) (.branch 51 (.leaf 1279559554) (.leaf 1250142421)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1221521494) (.leaf 1193669683)) (.branch 55 (.leaf 1166561057) (.leaf 1140170779))) (.branch 58 (.branch 57 (.leaf 1114475052) (.leaf 1089451073)) (.branch 59 (.leaf 1065076975) (.leaf 1041331791))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1018195402) (.branch 62 (.leaf 995648498) (.leaf 973672545))) (.branch 65 (.branch 64 (.leaf 952249737) (.leaf 931362973)) (.branch 66 (.leaf 910995814) (.leaf 891132459)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 871757712) (.leaf 852856952)) (.branch 70 (.leaf 834416112) (.leaf 816421651))) (.branch 73 (.branch 72 (.leaf 798860526) (.leaf 781720178)) (.branch 74 (.leaf 764988502) (.leaf 748653834))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 732704926) (.branch 77 (.leaf 717130929) (.leaf 701921379))) (.branch 80 (.branch 79 (.leaf 687066175) (.leaf 672555568)) (.branch 81 (.leaf 658380144) (.leaf 644530808)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 630998776) (.leaf 617775555)) (.branch 85 (.leaf 604852937) (.leaf 592222982))) (.branch 88 (.branch 87 (.leaf 579878012) (.leaf 567810598)) (.branch 89 (.leaf 556013548) (.leaf 544479902)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 533202919) (.branch 92 (.leaf 522176070) (.leaf 511393029))) (.branch 95 (.branch 94 (.leaf 500847666) (.leaf 490534039)) (.branch 96 (.leaf 480446386) (.leaf 470579121)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 460926822) (.leaf 451484232)) (.branch 100 (.leaf 442246246) (.leaf 433207910))) (.branch 103 (.branch 102 (.leaf 424364413) (.leaf 415711083)) (.branch 104 (.leaf 407243384) (.leaf 398956905))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390847363) (.leaf 382910593)) (.branch 108 (.leaf 375142547) (.leaf 367539287))) (.branch 111 (.branch 110 (.leaf 360096985) (.leaf 352811918)) (.branch 112 (.leaf 345680461) (.leaf 338699088)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331864369) (.leaf 325172961)) (.branch 116 (.leaf 318621613) (.leaf 312207158))) (.branch 119 (.branch 118 (.leaf 305926510) (.leaf 299776666)) (.branch 120 (.leaf 293754696) (.leaf 287857750)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 575).prefactor = (4679594532903853/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 575).cutoff/(generalMeanRows 575).c)).2 =
    (77616106044777/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 575).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 575).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 575).q*(generalMeanRows 575).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 575).q*(generalMeanRows 575).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 575).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 575

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 575).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 575).criticalRate j.val*(generalMeanRows 575).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 575).c*(generalMeanRows 575).criticalPoint j.val)).2-
      (generalMeanRows 575).J/2-(generalMeanRows 575).error (generalMeanGrid j.val)+
      (generalMeanRows 575).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 575).c)).2-
      (generalMeanRows 575).J/2-(generalMeanRows 575).error 4 := by
  have he : (generalMeanRows 575).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 575) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 575)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0575

/-! Kernel-checked entropy margins for general spectral rectangle 576. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0576
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5007331356) (.branch 2 (.leaf 4837451229) (.leaf 4675157018))) (.branch 5 (.branch 4 (.leaf 4520015899) (.leaf 4371625643)) (.branch 6 (.leaf 4229611943) (.leaf 4093626033)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3963342556) (.leaf 3838457649)) (.branch 10 (.leaf 3718687220) (.leaf 3603765396))) (.branch 13 (.branch 12 (.leaf 3493443113) (.leaf 3387486845)) (.branch 14 (.leaf 3285677443) (.leaf 3187809081))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3093688295) (.branch 17 (.leaf 3003133100) (.leaf 2915972194))) (.branch 20 (.branch 19 (.leaf 2832044208) (.leaf 2751197037)) (.branch 21 (.leaf 2673287216) (.leaf 2598179341)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2525745543) (.leaf 2455864998)) (.branch 25 (.leaf 2388423477) (.leaf 2323312923))) (.branch 28 (.branch 27 (.leaf 2260431069) (.leaf 2199681073)) (.branch 29 (.leaf 2140971188) (.leaf 2084214449)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2029328385) (.branch 32 (.leaf 1976234753) (.leaf 1924859282))) (.branch 35 (.branch 34 (.leaf 1875131443) (.leaf 1826984233)) (.branch 36 (.leaf 1780353967) (.leaf 1735180089)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1691404995) (.leaf 1648973868)) (.branch 40 (.leaf 1607834519) (.leaf 1567937241))) (.branch 43 (.branch 42 (.leaf 1529234676) (.leaf 1491681681)) (.branch 44 (.leaf 1455235211) (.leaf 1419854207))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1385499485) (.branch 47 (.leaf 1352133641) (.leaf 1319720952))) (.branch 50 (.branch 49 (.leaf 1288227293) (.leaf 1257620050)) (.branch 51 (.leaf 1227868041) (.leaf 1198941447)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1170811738) (.leaf 1143451607)) (.branch 55 (.leaf 1116834914) (.leaf 1090936619))) (.branch 58 (.branch 57 (.leaf 1065732734) (.leaf 1041200269)) (.branch 59 (.leaf 1017317181) (.leaf 994062331))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 971415436) (.branch 62 (.leaf 949357031) (.leaf 927868429))) (.branch 65 (.branch 64 (.leaf 906931683) (.leaf 886529552)) (.branch 66 (.leaf 866645466) (.leaf 847263499)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 828368332) (.leaf 809945232)) (.branch 70 (.leaf 791980021) (.leaf 774459052))) (.branch 73 (.branch 72 (.leaf 757369185) (.leaf 740697764)) (.branch 74 (.leaf 724432596) (.leaf 708561929))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 693074433) (.branch 77 (.leaf 677959184) (.leaf 663205643))) (.branch 80 (.branch 79 (.leaf 648803640) (.leaf 634743361)) (.branch 81 (.leaf 621015329) (.leaf 607610393)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 594519711) (.leaf 581734741)) (.branch 85 (.leaf 569247224) (.leaf 557049177))) (.branch 88 (.branch 87 (.leaf 545132880) (.leaf 533490862)) (.branch 89 (.leaf 522115897) (.leaf 511000989)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 500139367) (.branch 92 (.leaf 489524473) (.leaf 479149955))) (.branch 95 (.branch 94 (.leaf 469009658) (.leaf 459097619)) (.branch 96 (.leaf 449408057) (.leaf 439935367)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 430674114) (.leaf 421619025)) (.branch 100 (.leaf 412764984) (.leaf 404107029))) (.branch 103 (.branch 102 (.leaf 395640339) (.leaf 387360238)) (.branch 104 (.leaf 379262182) (.leaf 371341760))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 363594686) (.leaf 356016794)) (.branch 108 (.leaf 348604039) (.leaf 341352485))) (.branch 111 (.branch 110 (.leaf 334258308) (.leaf 327317789)) (.branch 112 (.leaf 320527310) (.leaf 313883353)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 307382494) (.leaf 301021404)) (.branch 116 (.leaf 294796838) (.leaf 288705643))) (.branch 119 (.branch 118 (.leaf 282744745) (.leaf 276911153)) (.branch 120 (.leaf 271201953) (.leaf 265614308)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 576).prefactor = (2347879449027221/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 576).cutoff/(generalMeanRows 576).c)).2 =
    (190280848904929/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 576).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 576).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 576).q*(generalMeanRows 576).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 576).q*(generalMeanRows 576).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 576).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 576

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 576).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 576).criticalRate j.val*(generalMeanRows 576).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 576).c*(generalMeanRows 576).criticalPoint j.val)).2-
      (generalMeanRows 576).J/2-(generalMeanRows 576).error (generalMeanGrid j.val)+
      (generalMeanRows 576).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 576).c)).2-
      (generalMeanRows 576).J/2-(generalMeanRows 576).error 4 := by
  have he : (generalMeanRows 576).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 576) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 576)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0576

/-! Kernel-checked entropy margins for general spectral rectangle 577. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0577
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5076190833) (.branch 2 (.leaf 4906422839) (.leaf 4744193435))) (.branch 5 (.branch 4 (.leaf 4589073144) (.leaf 4440662837)) (.branch 6 (.leaf 4298591078) (.leaf 4162511765)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4032102012) (.leaf 3907060253)) (.branch 10 (.leaf 3787104531) (.leaf 3671970958))) (.branch 13 (.branch 12 (.leaf 3561412318) (.leaf 3455196808)) (.branch 14 (.leaf 3353106884) (.leaf 3254938217))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3160498741) (.branch 17 (.leaf 3069607778) (.leaf 2982095243))) (.branch 20 (.branch 19 (.leaf 2897800912) (.leaf 2816573747)) (.branch 21 (.leaf 2738271282) (.leaf 2662759050)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2589910060) (.leaf 2519604314)) (.branch 25 (.leaf 2451728354) (.leaf 2386174851))) (.branch 28 (.branch 27 (.leaf 2322842220) (.leaf 2261634260)) (.branch 29 (.leaf 2202459828) (.leaf 2145232526)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2089870421) (.branch 32 (.leaf 2036295771) (.leaf 1984434782))) (.branch 35 (.branch 34 (.leaf 1934217374) (.leaf 1885576965)) (.branch 36 (.leaf 1838450269) (.leaf 1792777110)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1748500239) (.leaf 1705565176)) (.branch 40 (.leaf 1663920051) (.leaf 1623515459))) (.branch 43 (.branch 42 (.leaf 1584304327) (.leaf 1546241783)) (.branch 44 (.leaf 1509285039) (.leaf 1473393277))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1438527546) (.branch 47 (.leaf 1404650657) (.leaf 1371727096))) (.branch 50 (.branch 49 (.leaf 1339722935) (.leaf 1308605745)) (.branch 51 (.leaf 1278344522) (.leaf 1248909615)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1220272652) (.leaf 1192406481)) (.branch 55 (.leaf 1165285101) (.leaf 1138883612))) (.branch 58 (.branch 57 (.leaf 1113178155) (.leaf 1088145863)) (.branch 59 (.leaf 1063764810) (.leaf 1040013968))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1016873159) (.branch 62 (.leaf 994323018) (.leaf 972344954))) (.branch 65 (.branch 64 (.leaf 950921108) (.leaf 930034326)) (.branch 66 (.leaf 909668119) (.leaf 889806635)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 870434630) (.leaf 851537439)) (.branch 70 (.leaf 833100949) (.leaf 815111574))) (.branch 73 (.branch 72 (.leaf 797556231) (.leaf 780422320)) (.branch 74 (.leaf 763697697) (.leaf 747370659))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 731429923) (.branch 77 (.leaf 715864606) (.leaf 700664209))) (.branch 80 (.branch 79 (.leaf 685818599) (.leaf 671317997)) (.branch 81 (.leaf 657152958) (.leaf 643314360)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 629793390) (.leaf 616581530)) (.branch 85 (.leaf 603670546) (.leaf 591052476))) (.branch 88 (.branch 87 (.leaf 578719617) (.leaf 566664520)) (.branch 89 (.leaf 554879971) (.leaf 543358991)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 532094818) (.branch 92 (.leaf 521080907) (.leaf 510310915))) (.branch 95 (.branch 94 (.leaf 499778694) (.leaf 489478288)) (.branch 96 (.leaf 479403920) (.leaf 469549988)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 459911061) (.leaf 450481864)) (.branch 100 (.leaf 441257285) (.leaf 432232355))) (.branch 103 (.branch 102 (.leaf 423402256) (.leaf 414762304)) (.branch 104 (.leaf 406307952) (.leaf 398034784))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389938505) (.leaf 382014944)) (.branch 108 (.leaf 374260044) (.leaf 366669863))) (.branch 111 (.branch 110 (.leaf 359240565) (.leaf 351968420)) (.branch 112 (.leaf 344849798) (.leaf 337881170)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331059097) (.leaf 324380235)) (.branch 116 (.leaf 317841327) (.leaf 311439202))) (.branch 119 (.branch 118 (.leaf 305170772) (.leaf 299033030)) (.branch 120 (.leaf 293023043) (.leaf 287137958)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 577).prefactor = (4666168028488871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 577).cutoff/(generalMeanRows 577).c)).2 =
    (385227461241481/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 577).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 577).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 577).q*(generalMeanRows 577).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 577).q*(generalMeanRows 577).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 577).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 577

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 577).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 577).criticalRate j.val*(generalMeanRows 577).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 577).c*(generalMeanRows 577).criticalPoint j.val)).2-
      (generalMeanRows 577).J/2-(generalMeanRows 577).error (generalMeanGrid j.val)+
      (generalMeanRows 577).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 577).c)).2-
      (generalMeanRows 577).J/2-(generalMeanRows 577).error 4 := by
  have he : (generalMeanRows 577).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 577) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 577)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0577

/-! Kernel-checked entropy margins for general spectral rectangle 578. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0578
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5009796901) (.branch 2 (.leaf 4839877105) (.leaf 4677531075))) (.branch 5 (.branch 4 (.leaf 4522327652) (.leaf 4373866112)) (.branch 6 (.leaf 4231773511) (.leaf 4095702313)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3965328270) (.leaf 3840348519)) (.branch 10 (.leaf 3720479868) (.leaf 3605457252))) (.branch 13 (.branch 12 (.leaf 3495032332) (.leaf 3388972227)) (.branch 14 (.leaf 3287058368) (.leaf 3189085443))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3094860443) (.branch 17 (.leaf 3004201788) (.leaf 2916938528))) (.branch 20 (.branch 19 (.leaf 2832909607) (.leaf 2751963190)) (.branch 21 (.leaf 2673956045) (.leaf 2598752971)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2526226268) (.leaf 2456255258)) (.branch 25 (.leaf 2388725829) (.leaf 2323530023))) (.branch 28 (.branch 27 (.leaf 2260565647) (.leaf 2199735920)) (.branch 29 (.leaf 2140949136) (.leaf 2084118358)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2029161129) (.branch 32 (.leaf 1975999208) (.leaf 1924558317))) (.branch 35 (.branch 34 (.leaf 1874767910) (.leaf 1826560958)) (.branch 36 (.leaf 1779873743) (.leaf 1734645671)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1690819094) (.leaf 1648339144)) (.branch 40 (.leaf 1607153580) (.leaf 1567212637))) (.branch 43 (.branch 42 (.leaf 1528468898) (.leaf 1490877158)) (.branch 44 (.leaf 1454394309) (.leaf 1418979224))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1384592654) (.branch 47 (.leaf 1351197125) (.leaf 1318756848))) (.branch 50 (.branch 49 (.leaf 1287237629) (.leaf 1256606785)) (.branch 51 (.leaf 1226833068) (.leaf 1197886589)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1169738750) (.leaf 1142362181)) (.branch 55 (.leaf 1115730674) (.leaf 1089819124))) (.branch 58 (.branch 57 (.leaf 1064603482) (.leaf 1040060694)) (.branch 59 (.leaf 1016168657) (.leaf 992906171))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 970252895) (.branch 62 (.leaf 948189308) (.leaf 926696667))) (.branch 65 (.branch 64 (.leaf 905756971) (.leaf 885352927)) (.branch 66 (.leaf 865467914) (.leaf 846085955)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 827191686) (.leaf 808770325)) (.branch 70 (.leaf 790807650) (.leaf 773289972))) (.branch 73 (.branch 72 (.leaf 756204106) (.leaf 739537358)) (.branch 74 (.leaf 723277495) (.leaf 707412727))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 691931689) (.branch 77 (.leaf 676823421) (.leaf 662077351))) (.branch 80 (.branch 79 (.leaf 647683277) (.leaf 633631353)) (.branch 81 (.leaf 619912073) (.leaf 606516257)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 593435037) (.leaf 580659842)) (.branch 85 (.leaf 568182391) (.leaf 555994676))) (.branch 88 (.branch 87 (.leaf 544088953) (.leaf 532457731)) (.branch 89 (.leaf 521093762) (.leaf 509990030)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 499139746) (.branch 92 (.leaf 488536332) (.leaf 478173420))) (.branch 95 (.branch 94 (.leaf 468044839) (.leaf 458144610)) (.branch 96 (.leaf 448466936) (.leaf 439006200)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 429756952) (.leaf 420713907)) (.branch 100 (.leaf 411871938) (.leaf 403226070))) (.branch 103 (.branch 102 (.leaf 394771472) (.leaf 386503458)) (.branch 104 (.leaf 378417476) (.leaf 370509103))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 362774046) (.leaf 355208132)) (.branch 108 (.leaf 347807307) (.leaf 340567629))) (.branch 111 (.branch 110 (.leaf 333485267) (.leaf 326556495)) (.branch 112 (.leaf 319777692) (.leaf 313145332)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 306655988) (.leaf 300306323)) (.branch 116 (.leaf 294093093) (.leaf 288013136))) (.branch 119 (.branch 118 (.leaf 282063378) (.leaf 276240822)) (.branch 120 (.leaf 270542554) (.leaf 264965731)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 578).prefactor = (4682419641117237/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 578).cutoff/(generalMeanRows 578).c)).2 =
    (94427157206863/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 578).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 578).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 578).q*(generalMeanRows 578).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 578).q*(generalMeanRows 578).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 578).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 578

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 578).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 578).criticalRate j.val*(generalMeanRows 578).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 578).c*(generalMeanRows 578).criticalPoint j.val)).2-
      (generalMeanRows 578).J/2-(generalMeanRows 578).error (generalMeanGrid j.val)+
      (generalMeanRows 578).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 578).c)).2-
      (generalMeanRows 578).J/2-(generalMeanRows 578).error 4 := by
  have he : (generalMeanRows 578).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 578) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 578)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0578

/-! Kernel-checked entropy margins for general spectral rectangle 579. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0579
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5029605557) (.branch 2 (.leaf 4859062492) (.leaf 4696106944))) (.branch 5 (.branch 4 (.leaf 4540307937) (.leaf 4391264879)) (.branch 6 (.leaf 4248604906) (.leaf 4111980522)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3981067478) (.leaf 3855562874)) (.branch 10 (.leaf 3735183451) (.leaf 3619664042))) (.branch 13 (.branch 12 (.leaf 3508756185) (.leaf 3402226854)) (.branch 14 (.leaf 3299857308) (.leaf 3201442050))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3106787869) (.branch 17 (.leaf 3015712969) (.leaf 2928046173))) (.branch 20 (.branch 19 (.leaf 2843626187) (.leaf 2762300929)) (.branch 21 (.leaf 2683926915) (.leaf 2608368684)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2535498273) (.leaf 2465194738)) (.branch 25 (.leaf 2397343699) (.leaf 2331836926))) (.branch 28 (.branch 27 (.leaf 2268571957) (.leaf 2207451740)) (.branch 29 (.leaf 2148384300) (.leaf 2091282431)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2036063412) (.branch 32 (.leaf 1982648737) (.leaf 1930963870))) (.branch 35 (.branch 34 (.leaf 1880938007) (.leaf 1832503865)) (.branch 36 (.leaf 1785597479) (.leaf 1740158009)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1696127566) (.leaf 1653451047)) (.branch 40 (.leaf 1612075980) (.leaf 1571952374))) (.branch 43 (.branch 42 (.leaf 1533032591) (.leaf 1495271210)) (.branch 44 (.leaf 1458624911) (.leaf 1423052362))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1388514113) (.branch 47 (.leaf 1354972497) (.leaf 1322391533))) (.branch 50 (.branch 49 (.leaf 1290736841) (.leaf 1259975560)) (.branch 51 (.leaf 1230076265) (.leaf 1201008899)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1172744700) (.leaf 1145256135)) (.branch 55 (.leaf 1118516841) (.leaf 1092501567))) (.branch 58 (.branch 57 (.leaf 1067186113) (.leaf 1042547286)) (.branch 59 (.leaf 1018562845) (.leaf 995211459))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 972472660) (.branch 62 (.leaf 950326800) (.leaf 928755018))) (.branch 65 (.branch 64 (.leaf 907739196) (.leaf 887261930)) (.branch 66 (.leaf 867306491) (.leaf 847856797)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 828897382) (.leaf 810413368)) (.branch 70 (.leaf 792390439) (.leaf 774814814))) (.branch 73 (.branch 72 (.leaf 757673223) (.leaf 740952885)) (.branch 74 (.leaf 724641486) (.leaf 708727158))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 693198461) (.branch 77 (.leaf 678044361) (.leaf 663254215))) (.branch 80 (.branch 79 (.leaf 648817756) (.leaf 634725071)) (.branch 81 (.leaf 620966591) (.leaf 607533076)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 594415600) (.leaf 581605537)) (.branch 85 (.leaf 569094550) (.leaf 556874580))) (.branch 88 (.branch 87 (.leaf 544937833) (.leaf 533276770)) (.branch 89 (.leaf 521884096) (.leaf 510752753)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 499875906) (.branch 92 (.leaf 489246939) (.leaf 478859443))) (.branch 95 (.branch 94 (.leaf 468707208) (.leaf 458784220)) (.branch 96 (.leaf 449084648) (.leaf 439602838)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 430333309) (.leaf 421270746)) (.branch 100 (.leaf 412409991) (.leaf 403746039))) (.branch 103 (.branch 102 (.leaf 395274035) (.leaf 386989263)) (.branch 104 (.leaf 378887146) (.leaf 370963238))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 363213222) (.leaf 355632902)) (.branch 108 (.leaf 348218201) (.leaf 340965158))) (.branch 111 (.branch 110 (.leaf 333869922) (.leaf 326928748)) (.branch 112 (.leaf 320137994) (.leaf 313494119)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 306993678) (.leaf 300633318)) (.branch 116 (.leaf 294409778) (.leaf 288319883))) (.branch 119 (.branch 118 (.leaf 282360543) (.leaf 276528748)) (.branch 120 (.leaf 270821570) (.leaf 265236154)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 579).prefactor = (4685250061506981/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 579).cutoff/(generalMeanRows 579).c)).2 =
    (18743183834761/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 579).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 579).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 579).q*(generalMeanRows 579).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 579).q*(generalMeanRows 579).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 579).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 579

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 579).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 579).criticalRate j.val*(generalMeanRows 579).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 579).c*(generalMeanRows 579).criticalPoint j.val)).2-
      (generalMeanRows 579).J/2-(generalMeanRows 579).error (generalMeanGrid j.val)+
      (generalMeanRows 579).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 579).c)).2-
      (generalMeanRows 579).J/2-(generalMeanRows 579).error 4 := by
  have he : (generalMeanRows 579).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 579) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 579)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0579

/-! Kernel-checked entropy margins for general spectral rectangle 580. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0580
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4964600428) (.branch 2 (.leaf 4793933728) (.leaf 4630889629))) (.branch 5 (.branch 4 (.leaf 4475035427) (.leaf 4325968892)) (.branch 6 (.leaf 4183315611) (.leaf 4046726617)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3915876265) (.leaf 3790460328)) (.branch 10 (.leaf 3670194279) (.leaf 3554811749))) (.branch 13 (.branch 12 (.leaf 3444063126) (.leaf 3337714286)) (.branch 14 (.leaf 3235545440) (.leaf 3137350089))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3042934062) (.branch 17 (.leaf 2952114646) (.leaf 2864719781))) (.branch 20 (.branch 19 (.leaf 2780587332) (.leaf 2699564408)) (.branch 21 (.leaf 2621506748) (.leaf 2546278145)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2473749925) (.leaf 2403800452)) (.branch 25 (.leaf 2336314688) (.leaf 2271183770))) (.branch 28 (.branch 27 (.leaf 2208304626) (.leaf 2147579616)) (.branch 29 (.leaf 2088916202) (.leaf 2032226637)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1977427679) (.branch 32 (.leaf 1924440319) (.leaf 1873189538))) (.branch 35 (.branch 34 (.leaf 1823604069) (.leaf 1775616184)) (.branch 36 (.leaf 1729161484) (.leaf 1684178719)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1640609602) (.leaf 1598398646)) (.branch 40 (.leaf 1557493012) (.leaf 1517842355))) (.branch 43 (.branch 42 (.leaf 1479398696) (.leaf 1442116286)) (.branch 44 (.leaf 1405951492) (.leaf 1370862679))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1336810105) (.branch 47 (.leaf 1303755823) (.leaf 1271663585))) (.branch 50 (.branch 49 (.leaf 1240498752) (.leaf 1210228215)) (.branch 51 (.leaf 1180820312) (.leaf 1152244757)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1124472568) (.leaf 1097476004)) (.branch 55 (.leaf 1071228499) (.leaf 1045704608))) (.branch 58 (.branch 57 (.leaf 1020879947) (.leaf 996731146)) (.branch 59 (.leaf 973235793) (.leaf 950372395))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 928120328) (.branch 62 (.leaf 906459797) (.leaf 885371798))) (.branch 65 (.branch 64 (.leaf 864838078) (.leaf 844841102)) (.branch 66 (.leaf 825364018) (.leaf 806390628)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 787905352) (.leaf 769893207)) (.branch 70 (.leaf 752339775) (.leaf 735231178))) (.branch 73 (.branch 72 (.leaf 718554054) (.leaf 702295538)) (.branch 74 (.leaf 686443231) (.leaf 670985189))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 655909897) (.branch 77 (.leaf 641206253) (.leaf 626863549))) (.branch 80 (.branch 79 (.leaf 612871454) (.leaf 599219999)) (.branch 81 (.leaf 585899562) (.leaf 572900851)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 560214891) (.leaf 547833014)) (.branch 85 (.leaf 535746841) (.leaf 523948276))) (.branch 88 (.branch 87 (.leaf 512429490) (.leaf 501182910)) (.branch 89 (.leaf 490201213) (.leaf 479477314)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 469004352) (.branch 92 (.leaf 458775690) (.leaf 448784900))) (.branch 95 (.branch 94 (.leaf 439025754) (.leaf 429492222)) (.branch 96 (.leaf 420178460) (.leaf 411078804)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 402187763) (.leaf 393500014)) (.branch 100 (.leaf 385010394) (.leaf 376713895))) (.branch 103 (.branch 102 (.leaf 368605658) (.leaf 360680967)) (.branch 104 (.leaf 352935246) (.leaf 345364053))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337963071) (.leaf 330728112)) (.branch 108 (.leaf 323655105) (.leaf 316740096))) (.branch 111 (.branch 110 (.leaf 309979243) (.leaf 303368810)) (.branch 112 (.leaf 296905168) (.leaf 290584786)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284404233) (.leaf 278360171)) (.branch 116 (.leaf 272449352) (.leaf 266668618))) (.branch 119 (.branch 118 (.leaf 261014894) (.leaf 255485189)) (.branch 120 (.leaf 250076592) (.leaf 244786267)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 580).prefactor = (235085211941433/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 580).cutoff/(generalMeanRows 580).c)).2 =
    (367400955493631/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 580).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 580).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 580).q*(generalMeanRows 580).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 580).q*(generalMeanRows 580).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 580).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 580

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 580).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 580).criticalRate j.val*(generalMeanRows 580).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 580).c*(generalMeanRows 580).criticalPoint j.val)).2-
      (generalMeanRows 580).J/2-(generalMeanRows 580).error (generalMeanGrid j.val)+
      (generalMeanRows 580).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 580).c)).2-
      (generalMeanRows 580).J/2-(generalMeanRows 580).error 4 := by
  have he : (generalMeanRows 580).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 580) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 580)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0580

/-! Kernel-checked entropy margins for general spectral rectangle 581. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0581
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4944700865) (.branch 2 (.leaf 4774662314) (.leaf 4612232353))) (.branch 5 (.branch 4 (.leaf 4456978108) (.leaf 4308497234)) (.branch 6 (.leaf 4166415250) (.leaf 4030383163)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3900075339) (.leaf 3775187600)) (.branch 10 (.leaf 3655435499) (.leaf 3540552775))) (.branch 13 (.branch 12 (.leaf 3430289949) (.leaf 3324413053)) (.branch 14 (.leaf 3222702475) (.leaf 3124951909))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3030967393) (.branch 17 (.leaf 2940566437) (.leaf 2853577216))) (.branch 20 (.branch 19 (.leaf 2769837835) (.leaf 2689195658)) (.branch 21 (.leaf 2611506681) (.leaf 2536634962)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2464452093) (.leaf 2394836710)) (.branch 25 (.leaf 2327674047) (.leaf 2262855515))) (.branch 28 (.branch 27 (.leaf 2200278315) (.leaf 2139845084)) (.branch 29 (.leaf 2081463553) (.leaf 2025046249)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1970510195) (.branch 32 (.leaf 1917776651) (.leaf 1866770859))) (.branch 35 (.branch 34 (.leaf 1817421813) (.leaf 1769662037)) (.branch 36 (.leaf 1723427387) (.leaf 1678656857)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1635292404) (.leaf 1593278779)) (.branch 40 (.leaf 1552563373) (.leaf 1513096072))) (.branch 43 (.branch 42 (.leaf 1474829117) (.leaf 1437716979)) (.branch 44 (.leaf 1401716235) (.leaf 1366785457))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1332885107) (.branch 47 (.leaf 1299977434) (.leaf 1268026379))) (.branch 50 (.branch 49 (.leaf 1236997492) (.leaf 1206857843)) (.branch 51 (.leaf 1177575946) (.leaf 1149121687)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1121466249) (.leaf 1094582051)) (.branch 55 (.leaf 1068442685) (.leaf 1043022856))) (.branch 58 (.branch 57 (.leaf 1018298327) (.leaf 994245868)) (.branch 59 (.leaf 970843208) (.leaf 948068985))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 925902703) (.branch 62 (.leaf 904324693) (.leaf 883316070))) (.branch 65 (.branch 64 (.leaf 862858699) (.leaf 842935157)) (.branch 66 (.leaf 823528700) (.leaf 804623235)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 786203285) (.leaf 768253963)) (.branch 70 (.leaf 750760945) (.leaf 733710446))) (.branch 73 (.branch 72 (.leaf 717089192) (.leaf 700884400)) (.branch 74 (.leaf 685083755) (.leaf 669675392))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 654647871) (.branch 77 (.leaf 639990164) (.leaf 625691632))) (.branch 80 (.branch 79 (.leaf 611742014) (.leaf 598131406)) (.branch 81 (.leaf 584850248) (.leaf 571889308)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 559239673) (.leaf 546892727)) (.branch 85 (.leaf 534840148) (.leaf 523073891))) (.branch 88 (.branch 87 (.leaf 511586176) (.leaf 500369481)) (.branch 89 (.leaf 489416528) (.leaf 478720275)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 468273907) (.branch 92 (.leaf 458070826) (.leaf 448104643))) (.branch 95 (.branch 94 (.leaf 438369171) (.leaf 428858415)) (.branch 96 (.leaf 419566566) (.leaf 410487994)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 401617242) (.leaf 392949016)) (.branch 100 (.leaf 384478185) (.leaf 376199768))) (.branch 103 (.branch 102 (.leaf 368108935) (.leaf 360200998)) (.branch 104 (.leaf 352471404) (.leaf 344915736))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337529702) (.leaf 330309136)) (.branch 108 (.leaf 323249989) (.leaf 316348327))) (.branch 111 (.branch 110 (.leaf 309600329) (.leaf 303002279)) (.branch 112 (.leaf 296550564) (.leaf 290241675)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284072194) (.leaf 278038800)) (.branch 116 (.leaf 272138263) (.leaf 266367438))) (.branch 119 (.branch 118 (.leaf 260723266) (.leaf 255202770)) (.branch 120 (.leaf 249803050) (.leaf 244521286)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 581).prefactor = (4698727855846389/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 581).cutoff/(generalMeanRows 581).c)).2 =
    (185122953812931/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 581).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 581).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 581).q*(generalMeanRows 581).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 581).q*(generalMeanRows 581).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 581).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 581

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 581).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 581).criticalRate j.val*(generalMeanRows 581).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 581).c*(generalMeanRows 581).criticalPoint j.val)).2-
      (generalMeanRows 581).J/2-(generalMeanRows 581).error (generalMeanGrid j.val)+
      (generalMeanRows 581).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 581).c)).2-
      (generalMeanRows 581).J/2-(generalMeanRows 581).error 4 := by
  have he : (generalMeanRows 581).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 581) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 581)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0581

/-! Kernel-checked entropy margins for general spectral rectangle 582. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0582
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4961922568) (.branch 2 (.leaf 4791291797) (.leaf 4628296115))) (.branch 5 (.branch 4 (.leaf 4472501141) (.leaf 4323503130)) (.branch 6 (.leaf 4180926294) (.leaf 4044420425)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3913658758) (.leaf 3788336052)) (.branch 10 (.leaf 3668166871) (.leaf 3552884026))) (.branch 13 (.branch 12 (.leaf 3442237170) (.leaf 3335991520)) (.branch 14 (.leaf 3233926698) (.leaf 3135835681))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3041523830) (.branch 17 (.leaf 2950808020) (.leaf 2863515827))) (.branch 20 (.branch 19 (.leaf 2779484794) (.leaf 2698561752)) (.branch 21 (.leaf 2620602195) (.leaf 2545469708)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2473035436) (.leaf 2403177592)) (.branch 25 (.leaf 2335781011) (.leaf 2270736725))) (.branch 28 (.branch 27 (.leaf 2207941578) (.leaf 2147297866)) (.branch 29 (.leaf 2088713001) (.leaf 2032099202)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1977373207) (.branch 32 (.leaf 1924456000) (.leaf 1873272562))) (.branch 35 (.branch 34 (.leaf 1823751640) (.leaf 1775825523)) (.branch 36 (.leaf 1729429844) (.leaf 1684503385)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1640987899) (.leaf 1598827947)) (.branch 40 (.leaf 1557970735) (.leaf 1518365975))) (.branch 43 (.branch 42 (.leaf 1479965741) (.leaf 1442724347)) (.branch 44 (.leaf 1406598217) (.leaf 1371545781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1337527360) (.branch 47 (.leaf 1304505074) (.leaf 1272442738))) (.branch 50 (.branch 49 (.leaf 1241305781) (.leaf 1211061160)) (.branch 51 (.leaf 1181677279) (.leaf 1153123918)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1125372160) (.leaf 1098394328)) (.branch 55 (.leaf 1072163922) (.leaf 1046655559))) (.branch 58 (.branch 57 (.leaf 1021844918) (.leaf 997708688)) (.branch 59 (.leaf 974224520) (.leaf 951370977))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 929127493) (.branch 62 (.leaf 907474330) (.leaf 886392537))) (.branch 65 (.branch 64 (.leaf 865863916) (.leaf 845870982)) (.branch 66 (.leaf 826396936) (.leaf 807425626)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 788941521) (.leaf 770929684)) (.branch 70 (.leaf 753375741) (.leaf 736265857))) (.branch 73 (.branch 72 (.leaf 719586713) (.leaf 703325482)) (.branch 74 (.leaf 687469806) (.leaf 672007778))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 656927918) (.branch 77 (.leaf 642219160) (.leaf 627870829))) (.branch 80 (.branch 79 (.leaf 613872626) (.leaf 600214614)) (.branch 81 (.leaf 586887200) (.leaf 573881119)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 561187426) (.leaf 548797478)) (.branch 85 (.leaf 536702922) (.leaf 524895685))) (.branch 88 (.branch 87 (.leaf 513367960) (.leaf 502112198)) (.branch 89 (.leaf 491121098) (.leaf 480387591)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 469904840) (.branch 92 (.leaf 459666223) (.leaf 449665329))) (.branch 95 (.branch 94 (.leaf 439895950) (.leaf 430352069)) (.branch 96 (.leaf 421027858) (.leaf 411917667)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 403016019) (.leaf 394317603)) (.branch 100 (.leaf 385817269) (.leaf 377510020))) (.branch 103 (.branch 102 (.leaf 369391008) (.leaf 361455528)) (.branch 104 (.leaf 353699013) (.leaf 346117029))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 338705271) (.leaf 331459556)) (.branch 108 (.leaf 324375823) (.leaf 317450124))) (.branch 111 (.branch 110 (.leaf 310678624) (.leaf 304057593)) (.branch 112 (.leaf 297583409) (.leaf 291252546)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285061578) (.leaf 279007171)) (.branch 116 (.leaf 273086083) (.leaf 267295159))) (.branch 119 (.branch 118 (.leaf 261631329) (.leaf 256091605)) (.branch 120 (.leaf 250673079) (.leaf 245372920)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 582).prefactor = (4715092869813547/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 582).cutoff/(generalMeanRows 582).c)).2 =
    (185122953812931/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 582).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 582).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 582).q*(generalMeanRows 582).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 582).q*(generalMeanRows 582).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 582).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 582

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 582).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 582).criticalRate j.val*(generalMeanRows 582).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 582).c*(generalMeanRows 582).criticalPoint j.val)).2-
      (generalMeanRows 582).J/2-(generalMeanRows 582).error (generalMeanGrid j.val)+
      (generalMeanRows 582).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 582).c)).2-
      (generalMeanRows 582).J/2-(generalMeanRows 582).error 4 := by
  have he : (generalMeanRows 582).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 582) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 582)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0582

/-! Kernel-checked entropy margins for general spectral rectangle 583. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0583
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4900863609) (.branch 2 (.leaf 4730105091) (.leaf 4567003882))) (.branch 5 (.branch 4 (.leaf 4411125516) (.leaf 4262066100)) (.branch 6 (.leaf 4119449647) (.leaf 3982925695)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3852167181) (.leaf 3726868530)) (.branch 10 (.leaf 3606743933) (.leaf 3491525801))) (.branch 13 (.branch 12 (.leaf 3380963356) (.leaf 3274821364)) (.branch 14 (.leaf 3172878977) (.leaf 3074928680))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2980775336) (.branch 17 (.leaf 2890235304) (.leaf 2803135638))) (.branch 20 (.branch 19 (.leaf 2719313352) (.leaf 2638614743)) (.branch 21 (.leaf 2560894767) (.leaf 2486016473)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2413850465) (.leaf 2344274423)) (.branch 25 (.leaf 2277172645) (.leaf 2212435635))) (.branch 28 (.branch 27 (.leaf 2149959711) (.leaf 2089646650)) (.branch 29 (.leaf 2031403351) (.leaf 1975141528)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1920777419) (.branch 32 (.leaf 1868231520) (.leaf 1817428331))) (.branch 35 (.branch 34 (.leaf 1768296126) (.leaf 1720766735)) (.branch 36 (.leaf 1674775336) (.leaf 1630260269)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1587162857) (.leaf 1545427237)) (.branch 40 (.leaf 1505000206) (.leaf 1465831075))) (.branch 43 (.branch 42 (.leaf 1427871530) (.leaf 1391075502)) (.branch 44 (.leaf 1355399051) (.leaf 1320800247))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1287239065) (.branch 47 (.leaf 1254677287) (.leaf 1223078404))) (.branch 50 (.branch 49 (.leaf 1192407529) (.leaf 1162631311)) (.branch 51 (.leaf 1133717861) (.leaf 1105636672)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1078358552) (.leaf 1051855559)) (.branch 55 (.leaf 1026100934) (.leaf 1001069048))) (.branch 58 (.branch 57 (.leaf 976735341) (.leaf 953076273)) (.branch 59 (.leaf 930069275) (.leaf 907692697))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 885925770) (.branch 62 (.leaf 864748560) (.leaf 844141929))) (.branch 65 (.branch 64 (.leaf 824087498) (.leaf 804567611)) (.branch 66 (.leaf 785565303) (.leaf 767064266)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 749048818) (.leaf 731503876)) (.branch 70 (.leaf 714414932) (.leaf 697768018))) (.branch 73 (.branch 72 (.leaf 681549692) (.leaf 665747007)) (.branch 74 (.leaf 650347495) (.leaf 635339139))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 620710360) (.branch 77 (.leaf 606449996) (.leaf 592547280))) (.branch 80 (.branch 79 (.leaf 578991830) (.leaf 565773625)) (.branch 81 (.leaf 552882998) (.leaf 540310613)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 528047457) (.leaf 516084824)) (.branch 85 (.leaf 504414302) (.leaf 493027765))) (.branch 88 (.branch 87 (.leaf 481917355) (.leaf 471075476)) (.branch 89 (.leaf 460494781) (.leaf 450168164)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440088749) (.branch 92 (.leaf 430249883) (.leaf 420645123))) (.branch 95 (.branch 94 (.leaf 411268234) (.leaf 402113174)) (.branch 96 (.leaf 393174092) (.leaf 384445322)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375921367) (.leaf 367596905)) (.branch 100 (.leaf 359466771) (.leaf 351525961))) (.branch 103 (.branch 102 (.leaf 343769618) (.leaf 336193032)) (.branch 104 (.leaf 328791633) (.leaf 321560985))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314496784) (.leaf 307594849)) (.branch 108 (.leaf 300851121) (.leaf 294261660))) (.branch 111 (.branch 110 (.leaf 287822636) (.leaf 281530328)) (.branch 112 (.leaf 275381124) (.leaf 269371508)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263498068) (.leaf 257757482)) (.branch 116 (.leaf 252146524) (.leaf 246662053))) (.branch 119 (.branch 118 (.leaf 241301017) (.leaf 236060446)) (.branch 120 (.leaf 230937450) (.leaf 225929216)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 583).prefactor = (2359108100871473/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 583).cutoff/(generalMeanRows 583).c)).2 =
    (44999189276971/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 583).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 583).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 583).q*(generalMeanRows 583).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 583).q*(generalMeanRows 583).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 583).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 583

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 583).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 583).criticalRate j.val*(generalMeanRows 583).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 583).c*(generalMeanRows 583).criticalPoint j.val)).2-
      (generalMeanRows 583).J/2-(generalMeanRows 583).error (generalMeanGrid j.val)+
      (generalMeanRows 583).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 583).c)).2-
      (generalMeanRows 583).J/2-(generalMeanRows 583).error 4 := by
  have he : (generalMeanRows 583).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 583) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 583)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0583

/-! Kernel-checked entropy margins for general spectral rectangle 584. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0584
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5285241377) (.branch 2 (.leaf 5118417221) (.leaf 4958917081))) (.branch 5 (.branch 4 (.leaf 4806320255) (.leaf 4660235969)) (.branch 6 (.leaf 4520300765) (.leaf 4386176164)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4257546580) (.leaf 4134117440)) (.branch 10 (.leaf 4015613496) (.leaf 3901777306))) (.branch 13 (.branch 12 (.leaf 3792367849) (.leaf 3687159276)) (.branch 14 (.leaf 3585939778) (.leaf 3488510550))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3394684844) (.branch 17 (.leaf 3304287113) (.leaf 3217152216))) (.branch 20 (.branch 19 (.leaf 3133124701) (.leaf 3052058133)) (.branch 21 (.leaf 2973814489) (.leaf 2898263589)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2825282586) (.leaf 2754755476)) (.branch 25 (.leaf 2686572664) (.leaf 2620630549))) (.branch 28 (.branch 27 (.leaf 2556831147) (.leaf 2495081735)) (.branch 29 (.leaf 2435294530) (.leaf 2377386379)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2321278480) (.branch 32 (.leaf 2266896120) (.leaf 2214168426))) (.branch 35 (.branch 34 (.leaf 2163028142) (.leaf 2113411411)) (.branch 36 (.leaf 2065257580) (.leaf 2018509011)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1973110910) (.leaf 1929011163)) (.branch 40 (.leaf 1886160187) (.leaf 1844510781))) (.branch 43 (.branch 42 (.leaf 1804018000) (.leaf 1764639025)) (.branch 44 (.leaf 1726333049) (.leaf 1689061164))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1652786260) (.branch 47 (.leaf 1617472926) (.leaf 1583087360))) (.branch 50 (.branch 49 (.leaf 1549597282) (.leaf 1516971856)) (.branch 51 (.leaf 1485181610) (.leaf 1454198370)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1423995185) (.leaf 1394546272)) (.branch 55 (.leaf 1365826951) (.leaf 1337813589))) (.branch 58 (.branch 57 (.leaf 1310483549) (.leaf 1283815138)) (.branch 59 (.leaf 1257787561) (.leaf 1232380877))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1207575953) (.branch 62 (.leaf 1183354429) (.leaf 1159698677))) (.branch 65 (.branch 64 (.leaf 1136591769) (.leaf 1114017437)) (.branch 66 (.leaf 1091960049) (.leaf 1070404574)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049336554) (.leaf 1028742079)) (.branch 70 (.leaf 1008607759) (.leaf 988920704))) (.branch 73 (.branch 72 (.leaf 969668494) (.leaf 950839165)) (.branch 74 (.leaf 932421184) (.leaf 914403431))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 896775178) (.branch 77 (.leaf 879526077) (.leaf 862646137))) (.branch 80 (.branch 79 (.leaf 846125714) (.leaf 829955490)) (.branch 81 (.leaf 814126465) (.leaf 798629938)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 783457498) (.leaf 768601011)) (.branch 85 (.leaf 754052607) (.leaf 739804669))) (.branch 88 (.branch 87 (.leaf 725849824) (.leaf 712180934)) (.branch 89 (.leaf 698791083) (.leaf 685673570)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 672821900) (.branch 92 (.leaf 660229779) (.leaf 647891098))) (.branch 95 (.branch 94 (.leaf 635799936) (.leaf 623950544)) (.branch 96 (.leaf 612337345) (.leaf 600954922)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 589798015) (.leaf 578861517)) (.branch 100 (.leaf 568140462) (.leaf 557630026))) (.branch 103 (.branch 102 (.leaf 547325520) (.leaf 537222383)) (.branch 104 (.leaf 527316180) (.leaf 517602596))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 508077433) (.leaf 498736605)) (.branch 108 (.leaf 489576134) (.leaf 480592146))) (.branch 111 (.branch 110 (.leaf 471780870) (.leaf 463138631)) (.branch 112 (.leaf 454661848) (.leaf 446347034)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 438190786) (.leaf 430189791)) (.branch 116 (.leaf 422340816) (.leaf 414640706))) (.branch 119 (.branch 118 (.leaf 407086389) (.leaf 399674863)) (.branch 120 (.leaf 392403200) (.leaf 385268544)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 584).prefactor = (574307420401741/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 584).cutoff/(generalMeanRows 584).c)).2 =
    (210290722998737/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 584).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 584).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 584).q*(generalMeanRows 584).c/2-2 = (5663/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable205.value]
    have hcontinuation : (generalMeanRows 584).q*(generalMeanRows 584).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 584).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 584

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 584).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 584).criticalRate j.val*(generalMeanRows 584).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 584).c*(generalMeanRows 584).criticalPoint j.val)).2-
      (generalMeanRows 584).J/2-(generalMeanRows 584).error (generalMeanGrid j.val)+
      (generalMeanRows 584).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 584).c)).2-
      (generalMeanRows 584).J/2-(generalMeanRows 584).error 4 := by
  have he : (generalMeanRows 584).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 584) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 584)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0584

/-! Kernel-checked entropy margins for general spectral rectangle 585. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0585
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4870467926) (.branch 2 (.leaf 4698457110) (.leaf 4534241899))) (.branch 5 (.branch 4 (.leaf 4377376904) (.leaf 4227448171)) (.branch 6 (.leaf 4084070444) (.leaf 3946884715)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3815556035) (.leaf 3689771551)) (.branch 10 (.leaf 3569238738) (.leaf 3453683798))) (.branch 13 (.branch 12 (.leaf 3342850219) (.leaf 3236497469)) (.branch 14 (.leaf 3134399797) (.leaf 3036345161))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2942134230) (.branch 17 (.leaf 2851579489) (.leaf 2764504406))) (.branch 20 (.branch 19 (.leaf 2680742676) (.leaf 2600137527)) (.branch 21 (.leaf 2522541076) (.leaf 2447813739)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2375823692) (.leaf 2306446361)) (.branch 25 (.leaf 2239563963) (.leaf 2175065074))) (.branch 28 (.branch 27 (.leaf 2112844231) (.leaf 2052801559)) (.branch 29 (.leaf 1994842435) (.leaf 1938877161)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1884820672) (.branch 32 (.leaf 1832592258) (.leaf 1782115305))) (.branch 35 (.branch 34 (.leaf 1733317059) (.leaf 1686128399)) (.branch 36 (.leaf 1640483625) (.leaf 1596320269)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1553578905) (.leaf 1512202982)) (.branch 40 (.leaf 1472138662) (.leaf 1433334671))) (.branch 43 (.branch 42 (.leaf 1395742155) (.leaf 1359314553)) (.branch 44 (.leaf 1324007465) (.leaf 1289778545))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1256587383) (.branch 47 (.leaf 1224395408) (.leaf 1193165787))) (.branch 50 (.branch 49 (.leaf 1162863338) (.leaf 1133454440)) (.branch 51 (.leaf 1104906955) (.leaf 1077190151)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1050274631) (.leaf 1024132265)) (.branch 55 (.leaf 998736126) (.leaf 974060429))) (.branch 58 (.branch 57 (.leaf 950080477) (.leaf 926772605)) (.branch 59 (.leaf 904114128) (.leaf 882083299))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 860659255) (.branch 62 (.leaf 839821984) (.leaf 819552276))) (.branch 65 (.branch 64 (.leaf 799831690) (.leaf 780642515)) (.branch 66 (.leaf 761967738) (.leaf 743791010)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 726096614) (.leaf 708869440)) (.branch 70 (.leaf 692094953) (.leaf 675759169))) (.branch 73 (.branch 72 (.leaf 659848628) (.leaf 644350376)) (.branch 74 (.leaf 629251935) (.leaf 614541287))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 600206852) (.branch 77 (.leaf 586237468) (.leaf 572622378))) (.branch 80 (.branch 79 (.leaf 559351203) (.leaf 546413935)) (.branch 81 (.leaf 533800916) (.leaf 521502826)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 509510667) (.leaf 497815749)) (.branch 85 (.leaf 486409679) (.leaf 475284350))) (.branch 88 (.branch 87 (.leaf 464431924) (.leaf 453844827)) (.branch 89 (.leaf 443515735) (.leaf 433437565)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 423603466) (.branch 92 (.leaf 414006807) (.leaf 404641173))) (.branch 95 (.branch 94 (.leaf 395500353) (.leaf 386578332)) (.branch 96 (.leaf 377869287) (.leaf 369367576)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 361067732) (.leaf 352964458)) (.branch 100 (.leaf 345052620) (.leaf 337327238))) (.branch 103 (.branch 102 (.leaf 329783486) (.leaf 322416681)) (.branch 104 (.leaf 315222281) (.leaf 308195879))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 301333198) (.leaf 294630086)) (.branch 108 (.leaf 288082513) (.leaf 281686565))) (.branch 111 (.branch 110 (.leaf 275438442) (.leaf 269334452)) (.branch 112 (.leaf 263371008) (.leaf 257544624)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 251851915) (.leaf 246289587)) (.branch 116 (.leaf 240854441) (.leaf 235543365))) (.branch 119 (.branch 118 (.leaf 230353332) (.leaf 225281400)) (.branch 120 (.leaf 220324705) (.leaf 215480464)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 585).prefactor = (4792615910112733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 585).cutoff/(generalMeanRows 585).c)).2 =
    (181060250090973/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 585).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 585).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 585).q*(generalMeanRows 585).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 585).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 585

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 585).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 585).criticalRate j.val*(generalMeanRows 585).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 585).c*(generalMeanRows 585).criticalPoint j.val)).2-
      (generalMeanRows 585).J/2-(generalMeanRows 585).error (generalMeanGrid j.val)+
      (generalMeanRows 585).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 585).c)).2-
      (generalMeanRows 585).J/2-(generalMeanRows 585).error 4 := by
  have he : (generalMeanRows 585).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 585) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 585)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0585

/-! Kernel-checked entropy margins for general spectral rectangle 586. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0586
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4986164821) (.branch 2 (.leaf 4812421803) (.leaf 4646520992))) (.branch 5 (.branch 4 (.leaf 4488014141) (.leaf 4336484671)) (.branch 6 (.leaf 4191544907) (.leaf 4052833614)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3920013790) (.leaf 3792770687)) (.branch 10 (.leaf 3670810031) (.leaf 3553856407))) (.branch 13 (.branch 12 (.leaf 3441651811) (.leaf 3333954324)) (.branch 14 (.leaf 3230536920) (.leaf 3131186370))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3035702248) (.branch 17 (.leaf 2943896019) (.leaf 2855590208))) (.branch 20 (.branch 19 (.leaf 2770617639) (.leaf 2688820724)) (.branch 21 (.leaf 2610050829) (.leaf 2534167672)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2461038775) (.leaf 2390538963)) (.branch 25 (.leaf 2322549892) (.leaf 2256959615))) (.branch 28 (.branch 27 (.leaf 2193662183) (.leaf 2132557270)) (.branch 29 (.leaf 2073549831) (.leaf 2016549776)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1961471675) (.branch 32 (.leaf 1908234476) (.leaf 1856761249))) (.branch 35 (.branch 34 (.leaf 1806978942) (.leaf 1758818155)) (.branch 36 (.leaf 1712212931) (.leaf 1667100557)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1623421381) (.leaf 1581118638)) (.branch 40 (.leaf 1540138291) (.leaf 1500428878))) (.branch 43 (.branch 42 (.leaf 1461941368) (.leaf 1424629032)) (.branch 44 (.leaf 1388447316) (.leaf 1353353724))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1319307708) (.branch 47 (.leaf 1286270562) (.leaf 1254205329))) (.branch 50 (.branch 49 (.leaf 1223076706) (.leaf 1192850960)) (.branch 51 (.leaf 1163495844) (.leaf 1134980522)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1107275500) (.leaf 1080352551)) (.branch 55 (.leaf 1054184657) (.leaf 1028745947))) (.branch 58 (.branch 57 (.leaf 1004011637) (.leaf 979957980)) (.branch 59 (.leaf 956562215) (.leaf 933802513))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 911657941) (.branch 62 (.leaf 890108410) (.leaf 869134641))) (.branch 65 (.branch 64 (.leaf 848718122) (.leaf 828841075)) (.branch 66 (.leaf 809486420) (.leaf 790637741)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 772279257) (.leaf 754395793)) (.branch 70 (.leaf 736972752) (.leaf 719996086))) (.branch 73 (.branch 72 (.leaf 703452275) (.leaf 687328302)) (.branch 74 (.leaf 671611630) (.leaf 656290178))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 641352308) (.branch 77 (.leaf 626786799) (.leaf 612582832))) (.branch 80 (.branch 79 (.leaf 598729970) (.leaf 585218147)) (.branch 81 (.leaf 572037645) (.leaf 559179085)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 546633411) (.leaf 534391874)) (.branch 85 (.leaf 522446025) (.leaf 510787694))) (.branch 88 (.branch 87 (.leaf 499408989) (.leaf 488302276)) (.branch 89 (.leaf 477460173) (.leaf 466875539)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 456541464) (.branch 92 (.leaf 446451260) (.leaf 436598454))) (.branch 95 (.branch 94 (.leaf 426976775) (.leaf 417580153)) (.branch 96 (.leaf 408402705) (.leaf 399438732)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 390682708) (.leaf 382129279)) (.branch 100 (.leaf 373773253) (.leaf 365609593))) (.branch 103 (.branch 102 (.leaf 357633413) (.leaf 349839976)) (.branch 104 (.leaf 342224679) (.leaf 334783060))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 327510784) (.leaf 320403642)) (.branch 108 (.leaf 313457547) (.leaf 306668528))) (.branch 111 (.branch 110 (.leaf 300032727) (.leaf 293546397)) (.branch 112 (.leaf 287205894) (.leaf 281007676)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 274948301) (.leaf 269024421)) (.branch 116 (.leaf 263232779) (.leaf 257570209))) (.branch 119 (.branch 118 (.leaf 252033628) (.leaf 246620040)) (.branch 120 (.leaf 241326526) (.leaf 236150246)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 586).prefactor = (1206461031885843/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 586).cutoff/(generalMeanRows 586).c)).2 =
    (73916644276707/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 586).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 586).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 586).q*(generalMeanRows 586).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 586).q*(generalMeanRows 586).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 586).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 586

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 586).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 586).criticalRate j.val*(generalMeanRows 586).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 586).c*(generalMeanRows 586).criticalPoint j.val)).2-
      (generalMeanRows 586).J/2-(generalMeanRows 586).error (generalMeanGrid j.val)+
      (generalMeanRows 586).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 586).c)).2-
      (generalMeanRows 586).J/2-(generalMeanRows 586).error 4 := by
  have he : (generalMeanRows 586).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 586) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 586)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0586

/-! Kernel-checked entropy margins for general spectral rectangle 587. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0587
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5259536161) (.branch 2 (.leaf 5091174654) (.leaf 4930266035))) (.branch 5 (.branch 4 (.leaf 4776380484) (.leaf 4629118803)) (.branch 6 (.leaf 4488109745) (.leaf 4353007620)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4223490162) (.leaf 4099256609)) (.branch 10 (.leaf 3980025970) (.leaf 3865535473))) (.branch 13 (.branch 12 (.leaf 3755539146) (.leaf 3649806544)) (.branch 14 (.leaf 3548121580) (.leaf 3450281471))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3356095769) (.branch 17 (.leaf 3265385481) (.leaf 3177982258))) (.branch 20 (.branch 19 (.leaf 3093727655) (.leaf 3012472451)) (.branch 21 (.leaf 2934076023) (.leaf 2858405768)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2785336575) (.leaf 2714750330)) (.branch 25 (.leaf 2646535465) (.leaf 2580586539))) (.branch 28 (.branch 27 (.leaf 2516803845) (.leaf 2455093056)) (.branch 29 (.leaf 2395364882) (.leaf 2337534767)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2281522595) (.branch 32 (.leaf 2227252423) (.leaf 2174652227))) (.branch 35 (.branch 34 (.leaf 2123653674) (.leaf 2074191900)) (.branch 36 (.leaf 2026205306) (.leaf 1979635372)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1934426474) (.leaf 1890525723)) (.branch 40 (.leaf 1847882806) (.leaf 1806449843))) (.branch 43 (.branch 42 (.leaf 1766181247) (.leaf 1727033601)) (.branch 44 (.leaf 1688965535) (.leaf 1651937612))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1615912228) (.branch 47 (.leaf 1580853505) (.leaf 1546727207))) (.branch 50 (.branch 49 (.leaf 1513500643) (.leaf 1481142591)) (.branch 51 (.leaf 1449623220) (.leaf 1418914013)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1388987702) (.leaf 1359818204)) (.branch 55 (.leaf 1331380556) (.leaf 1303650861))) (.branch 58 (.branch 57 (.leaf 1276606232) (.leaf 1250224743)) (.branch 59 (.leaf 1224485377) (.leaf 1199367985))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1174853242) (.branch 62 (.leaf 1150922602) (.leaf 1127558265))) (.branch 65 (.branch 64 (.leaf 1104743140) (.leaf 1082460808)) (.branch 66 (.leaf 1060695493) (.leaf 1039432026)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1018655825) (.leaf 998352857)) (.branch 70 (.leaf 978509623) (.leaf 959113122))) (.branch 73 (.branch 72 (.leaf 940150839) (.leaf 921610713)) (.branch 74 (.leaf 903481124) (.leaf 885750867))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 868409139) (.branch 77 (.leaf 851445516) (.leaf 834849939))) (.branch 80 (.branch 79 (.leaf 818612698) (.leaf 802724416)) (.branch 81 (.leaf 787176033) (.leaf 771958798)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 757064247) (.leaf 742484199)) (.branch 85 (.leaf 728210740) (.leaf 714236212))) (.branch 88 (.branch 87 (.leaf 700553204) (.leaf 687154540)) (.branch 89 (.leaf 674033271) (.leaf 661182665)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 648596198) (.branch 92 (.leaf 636267546) (.leaf 624190579))) (.branch 95 (.branch 94 (.leaf 612359349) (.leaf 600768088)) (.branch 96 (.leaf 589411197) (.leaf 578283241)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 567378944) (.leaf 556693181)) (.branch 100 (.leaf 546220975) (.leaf 535957489))) (.branch 103 (.branch 102 (.leaf 525898020) (.leaf 516037999)) (.branch 104 (.leaf 506372980) (.leaf 496898642))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 487610778) (.leaf 478505296)) (.branch 108 (.leaf 469578213) (.leaf 460825652))) (.branch 111 (.branch 110 (.leaf 452243838) (.leaf 443829092)) (.branch 112 (.leaf 435577833) (.leaf 427486571)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 419551904) (.leaf 411770519)) (.branch 116 (.leaf 404139183) (.leaf 396654745))) (.branch 119 (.branch 118 (.leaf 389314133) (.leaf 382114347)) (.branch 120 (.leaf 375052465) (.leaf 368125633)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 587).prefactor = (4655449209567267/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 587).cutoff/(generalMeanRows 587).c)).2 =
    (419590669047169/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 587).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 587).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 587).q*(generalMeanRows 587).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 587).q*(generalMeanRows 587).cutoff/2-2 = (8158/3817:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable200.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 587).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 587

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 587).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 587).criticalRate j.val*(generalMeanRows 587).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 587).c*(generalMeanRows 587).criticalPoint j.val)).2-
      (generalMeanRows 587).J/2-(generalMeanRows 587).error (generalMeanGrid j.val)+
      (generalMeanRows 587).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 587).c)).2-
      (generalMeanRows 587).J/2-(generalMeanRows 587).error 4 := by
  have he : (generalMeanRows 587).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 587) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 587)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0587

/-! Kernel-checked entropy margins for general spectral rectangle 588. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0588
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5277264415) (.branch 2 (.leaf 5108335414) (.leaf 4946884422))) (.branch 5 (.branch 4 (.leaf 4792480170) (.leaf 4644722117)) (.branch 6 (.leaf 4503237761) (.leaf 4367680249)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4237726228) (.leaf 4113073922)) (.branch 10 (.leaf 3993441395) (.leaf 3878564986))) (.branch 13 (.branch 12 (.leaf 3768197896) (.leaf 3662108902)) (.branch 14 (.leaf 3560081190) (.leaf 3461911292))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3367408120) (.branch 17 (.leaf 3276392076) (.leaf 3188694244))) (.branch 20 (.branch 19 (.leaf 3104155644) (.leaf 3022626555)) (.branch 21 (.leaf 2943965876) (.leaf 2868040561)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2794725074) (.leaf 2723900905)) (.branch 25 (.leaf 2655456110) (.leaf 2589284890))) (.branch 28 (.branch 27 (.leaf 2525287205) (.leaf 2463368408)) (.branch 29 (.leaf 2403438909) (.leaf 2345413867)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2289212896) (.branch 32 (.leaf 2234759795) (.leaf 2181982301))) (.branch 35 (.branch 34 (.leaf 2130811848) (.leaf 2081183353)) (.branch 36 (.leaf 2033035012) (.leaf 1986308104)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1940946821) (.leaf 1896898094)) (.branch 40 (.leaf 1854111442) (.leaf 1812538821))) (.branch 43 (.branch 42 (.leaf 1772134492) (.leaf 1732854892)) (.branch 44 (.leaf 1694658510) (.leaf 1657505778))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1621358963) (.branch 47 (.leaf 1586182069) (.leaf 1551940741))) (.branch 50 (.branch 49 (.leaf 1518602181) (.leaf 1486135060)) (.branch 51 (.leaf 1454509447) (.leaf 1423696729)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1393669546) (.leaf 1364401727)) (.branch 55 (.leaf 1335868224) (.leaf 1308045061))) (.branch 58 (.branch 57 (.leaf 1280909273) (.leaf 1254438860)) (.branch 59 (.leaf 1228612735) (.leaf 1203410680))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1178813305) (.branch 62 (.leaf 1154802002) (.leaf 1131358912))) (.branch 65 (.branch 64 (.leaf 1108466884) (.leaf 1086109446)) (.branch 66 (.leaf 1064270766) (.leaf 1042935627)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1022089395) (.leaf 1001717993)) (.branch 70 (.leaf 981807873) (.leaf 962345993))) (.branch 73 (.branch 72 (.leaf 943319794) (.leaf 924717175)) (.branch 74 (.leaf 906526476) (.leaf 888736457))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 871336275) (.branch 77 (.leaf 854315473) (.leaf 837663957))) (.branch 80 (.branch 79 (.leaf 821371986) (.leaf 805430149)) (.branch 81 (.leaf 789829358) (.leaf 774560830)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 759616074) (.leaf 744986881)) (.branch 85 (.leaf 730665311) (.leaf 716643679))) (.branch 88 (.branch 87 (.leaf 702914550) (.leaf 689470723)) (.branch 89 (.leaf 676305226) (.leaf 663411305)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 650782413) (.branch 92 (.leaf 638412205) (.leaf 626294531))) (.branch 95 (.branch 94 (.leaf 614423422) (.leaf 602793090)) (.branch 96 (.leaf 591397918) (.leaf 580232453)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 569291401) (.leaf 558569620)) (.branch 100 (.leaf 548062116) (.leaf 537764034))) (.branch 103 (.branch 102 (.leaf 527670658) (.leaf 517777402)) (.branch 104 (.leaf 508079805) (.leaf 498573532))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 489254361) (.leaf 480118188)) (.branch 108 (.leaf 471161015) (.leaf 462378952))) (.branch 111 (.branch 110 (.leaf 453768210) (.leaf 445325101)) (.branch 112 (.leaf 437046029) (.leaf 428927494)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 420966083) (.leaf 413158469)) (.branch 116 (.leaf 405501410) (.leaf 397991745))) (.branch 119 (.branch 118 (.leaf 390626389) (.leaf 383402336)) (.branch 120 (.leaf 376316650) (.leaf 369366470)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 588).prefactor = (4671141274907949/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 588).cutoff/(generalMeanRows 588).c)).2 =
    (419590669047169/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 588).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 588).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 588).q*(generalMeanRows 588).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 588).q*(generalMeanRows 588).cutoff/2-2 = (8158/3817:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable200.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 588).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 588

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 588).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 588).criticalRate j.val*(generalMeanRows 588).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 588).c*(generalMeanRows 588).criticalPoint j.val)).2-
      (generalMeanRows 588).J/2-(generalMeanRows 588).error (generalMeanGrid j.val)+
      (generalMeanRows 588).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 588).c)).2-
      (generalMeanRows 588).J/2-(generalMeanRows 588).error 4 := by
  have he : (generalMeanRows 588).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 588) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 588)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0588

/-! Kernel-checked entropy margins for general spectral rectangle 589. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0589
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5120275667) (.branch 2 (.leaf 4951400768) (.leaf 4790038721))) (.branch 5 (.branch 4 (.leaf 4635758200) (.leaf 4488158506)) (.branch 6 (.leaf 4346866896) (.leaf 4211536195)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4081842656) (.leaf 3957484045)) (.branch 10 (.leaf 3838177914) (.leaf 3723660041))) (.branch 13 (.branch 12 (.leaf 3613683019) (.leaf 3508014980)) (.branch 14 (.leaf 3406438433) (.leaf 3308749202))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3214755469) (.branch 17 (.leaf 3124276885) (.leaf 3037143764))) (.branch 20 (.branch 19 (.leaf 2953196347) (.leaf 2872284116)) (.branch 21 (.leaf 2794265174) (.leaf 2719005666)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646379250) (.leaf 2576266605)) (.branch 25 (.leaf 2508554977) (.leaf 2443137765))) (.branch 28 (.branch 27 (.leaf 2379914123) (.leaf 2318788610)) (.branch 29 (.leaf 2259670847) (.leaf 2202475211)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2147120542) (.branch 32 (.leaf 2093529881) (.leaf 2041630209))) (.branch 35 (.branch 34 (.leaf 1991352222) (.leaf 1942630108)) (.branch 36 (.leaf 1895401348) (.leaf 1849606520)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1805189124) (.leaf 1762095418)) (.branch 40 (.leaf 1720274258) (.leaf 1679676955))) (.branch 43 (.branch 42 (.leaf 1640257137) (.leaf 1601970623)) (.branch 44 (.leaf 1564775299) (.leaf 1528631008))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1493499444) (.branch 47 (.leaf 1459344051) (.leaf 1426129932))) (.branch 50 (.branch 49 (.leaf 1393823757) (.leaf 1362393685)) (.branch 51 (.leaf 1331809281) (.leaf 1302041449)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1273062354) (.leaf 1244845369)) (.branch 55 (.leaf 1217365001) (.leaf 1190596843))) (.branch 58 (.branch 57 (.leaf 1164517514) (.leaf 1139104608)) (.branch 59 (.leaf 1114336649) (.leaf 1090193042))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1066654029) (.branch 62 (.leaf 1043700651) (.leaf 1021314706))) (.branch 65 (.branch 64 (.leaf 999478716) (.leaf 978175890)) (.branch 66 (.leaf 957390091) (.leaf 937105807)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 917308121) (.leaf 897982681)) (.branch 70 (.leaf 879115678) (.leaf 860693817))) (.branch 73 (.branch 72 (.leaf 842704295) (.leaf 825134780)) (.branch 74 (.leaf 807973388) (.leaf 791208664))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 774829561) (.branch 77 (.leaf 758825426) (.leaf 743185978))) (.branch 80 (.branch 79 (.leaf 727901293) (.leaf 712961792)) (.branch 81 (.leaf 698358223) (.leaf 684081646)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 670123423) (.leaf 656475204)) (.branch 85 (.leaf 643128914) (.leaf 630076742))) (.branch 88 (.branch 87 (.leaf 617311132) (.leaf 604824770)) (.branch 89 (.leaf 592610575) (.leaf 580661691)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 568971477) (.branch 92 (.leaf 557533498) (.leaf 546341517))) (.branch 95 (.branch 94 (.leaf 535389489) (.leaf 524671551)) (.branch 96 (.leaf 514182017) (.leaf 503915370)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 493866258) (.leaf 484029483)) (.branch 100 (.leaf 474400001) (.leaf 464972913))) (.branch 103 (.branch 102 (.leaf 455743460) (.leaf 446707018)) (.branch 104 (.leaf 437859093) (.leaf 429195319))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 420711450) (.leaf 412403355)) (.branch 108 (.leaf 404267021) (.leaf 396298538))) (.branch 111 (.branch 110 (.leaf 388494107) (.leaf 380850028)) (.branch 112 (.leaf 373362699) (.leaf 366028614)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358844359) (.leaf 351806609)) (.branch 116 (.leaf 344912125) (.leaf 338157751))) (.branch 119 (.branch 118 (.leaf 331540412) (.leaf 325057110)) (.branch 120 (.leaf 318704925) (.leaf 312481007)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 589).prefactor = (1168489071198761/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 589).cutoff/(generalMeanRows 589).c)).2 =
    (25086687421333/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 589).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 589).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 589).q*(generalMeanRows 589).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 589).q*(generalMeanRows 589).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 589).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 589

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 589).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 589).criticalRate j.val*(generalMeanRows 589).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 589).c*(generalMeanRows 589).criticalPoint j.val)).2-
      (generalMeanRows 589).J/2-(generalMeanRows 589).error (generalMeanGrid j.val)+
      (generalMeanRows 589).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 589).c)).2-
      (generalMeanRows 589).J/2-(generalMeanRows 589).error 4 := by
  have he : (generalMeanRows 589).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 589) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 589)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0589

/-! Kernel-checked entropy margins for general spectral rectangle 590. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0590
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5225434593) (.branch 2 (.leaf 5055620582) (.leaf 4893335038))) (.branch 5 (.branch 4 (.leaf 4738145295) (.leaf 4589649436)) (.branch 6 (.leaf 4447473615) (.leaf 4311269653)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4180712899) (.leaf 4055500296)) (.branch 10 (.leaf 3935348652) (.leaf 3819993072))) (.branch 13 (.branch 12 (.leaf 3709185545) (.leaf 3602693654)) (.branch 14 (.leaf 3500299415) (.leaf 3401798213))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3306997830) (.branch 17 (.leaf 3215717564) (.leaf 3127787414))) (.branch 20 (.branch 19 (.leaf 3043047340) (.leaf 2961346576)) (.branch 21 (.leaf 2882543007) (.leaf 2806502587)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2733098807) (.leaf 2662212202)) (.branch 25 (.leaf 2593729897) (.leaf 2527545185))) (.branch 28 (.branch 27 (.leaf 2463557135) (.leaf 2401670235)) (.branch 29 (.leaf 2341794050) (.leaf 2283842912)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2227735633) (.branch 32 (.leaf 2173395230) (.leaf 2120748675))) (.branch 35 (.branch 34 (.leaf 2069726661) (.leaf 2020263384)) (.branch 36 (.leaf 1972296333) (.leaf 1925766108)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1880616235) (.leaf 1836792998)) (.branch 40 (.leaf 1794245289) (.leaf 1752924457))) (.branch 43 (.branch 42 (.leaf 1712784171) (.leaf 1673780292)) (.branch 44 (.leaf 1635870754) (.leaf 1599015448))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1563176118) (.branch 47 (.leaf 1528316260) (.leaf 1494401027))) (.branch 50 (.branch 49 (.leaf 1461397143) (.leaf 1429272820)) (.branch 51 (.leaf 1397997678) (.leaf 1367542673)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1337880025) (.leaf 1308983158)) (.branch 55 (.leaf 1280826634) (.leaf 1253386095))) (.branch 58 (.branch 57 (.leaf 1226638213) (.leaf 1200560633)) (.branch 59 (.leaf 1175131926) (.leaf 1150331544))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1126139779) (.branch 62 (.leaf 1102537714) (.leaf 1079507194))) (.branch 65 (.branch 64 (.leaf 1057030781) (.leaf 1035091727)) (.branch 66 (.leaf 1013673934) (.leaf 992761928)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 972340828) (.leaf 952396317)) (.branch 70 (.leaf 932914620) (.leaf 913882472))) (.branch 73 (.branch 72 (.leaf 895287102) (.leaf 877116205)) (.branch 74 (.leaf 859357924) (.leaf 842000828))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 825033895) (.branch 77 (.leaf 808446492) (.leaf 792228359))) (.branch 80 (.branch 79 (.leaf 776369591) (.leaf 760860625)) (.branch 81 (.leaf 745692224) (.leaf 730855462)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 716341713) (.leaf 702142638)) (.branch 85 (.leaf 688250171) (.leaf 674656509))) (.branch 88 (.branch 87 (.leaf 661354101) (.leaf 648335638)) (.branch 89 (.leaf 635594044) (.leaf 623122464)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 610914257) (.branch 92 (.leaf 598962988) (.leaf 587262419))) (.branch 95 (.branch 94 (.leaf 575806500) (.leaf 564589365)) (.branch 96 (.leaf 553605323) (.leaf 542848849)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 532314583) (.leaf 521997321)) (.branch 100 (.leaf 511892006) (.leaf 501993728))) (.branch 103 (.branch 102 (.leaf 492297718) (.leaf 482799337)) (.branch 104 (.leaf 473494080) (.leaf 464377563))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 455445526) (.leaf 446693823)) (.branch 108 (.leaf 438118420) (.leaf 429715392))) (.branch 111 (.branch 110 (.leaf 421480920) (.leaf 413411283)) (.branch 112 (.leaf 405502861) (.leaf 397752126)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 390155643) (.leaf 382710064)) (.branch 116 (.leaf 375412127) (.leaf 368258652))) (.branch 119 (.branch 118 (.leaf 361246541) (.leaf 354372772)) (.branch 120 (.leaf 347634398) (.leaf 341028546)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 590).prefactor = (4689839073418193/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 590).cutoff/(generalMeanRows 590).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 590).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 590).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 590).q*(generalMeanRows 590).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 590).q*(generalMeanRows 590).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 590).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 590

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 590).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 590).criticalRate j.val*(generalMeanRows 590).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 590).c*(generalMeanRows 590).criticalPoint j.val)).2-
      (generalMeanRows 590).J/2-(generalMeanRows 590).error (generalMeanGrid j.val)+
      (generalMeanRows 590).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 590).c)).2-
      (generalMeanRows 590).J/2-(generalMeanRows 590).error 4 := by
  have he : (generalMeanRows 590).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 590) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 590)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0590

/-! Kernel-checked entropy margins for general spectral rectangle 591. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0591
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5172651587) (.branch 2 (.leaf 5002049247) (.leaf 4839036608))) (.branch 5 (.branch 4 (.leaf 4683177932) (.leaf 4534068423)) (.branch 6 (.leaf 4391331524) (.leaf 4254616509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4123596319) (.leaf 3997965629)) (.branch 10 (.leaf 3877439102) (.leaf 3761749811))) (.branch 13 (.branch 12 (.leaf 3650647821) (.leaf 3543898891)) (.branch 14 (.leaf 3441283304) (.leaf 3342594799))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3247639593) (.branch 17 (.leaf 3156235492) (.leaf 3068211076))) (.branch 20 (.branch 19 (.leaf 2983404950) (.leaf 2901665058)) (.branch 21 (.leaf 2822848051) (.leaf 2746818705)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2673449384) (.leaf 2602619548)) (.branch 25 (.leaf 2534215290) (.leaf 2468128917))) (.branch 28 (.branch 27 (.leaf 2404258554) (.leaf 2342507780)) (.branch 29 (.leaf 2282785294) (.leaf 2225004596)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2169083699) (.branch 32 (.leaf 2114944852) (.leaf 2062514291))) (.branch 35 (.branch 34 (.leaf 2011722005) (.leaf 1962501507)) (.branch 36 (.leaf 1914789638) (.leaf 1868526369)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1823654623) (.leaf 1780120106)) (.branch 40 (.leaf 1737871152) (.leaf 1696858574))) (.branch 43 (.branch 42 (.leaf 1657035527) (.leaf 1618357375)) (.branch 44 (.leaf 1580781575) (.leaf 1544267560))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1508776631) (.branch 47 (.leaf 1474271858) (.leaf 1440717988))) (.branch 50 (.branch 49 (.leaf 1408081350) (.leaf 1376329775)) (.branch 51 (.leaf 1345432520) (.leaf 1315360188)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1286084664) (.leaf 1257579043)) (.branch 55 (.leaf 1229817575) (.leaf 1202775602))) (.branch 58 (.branch 57 (.leaf 1176429504) (.leaf 1150756647)) (.branch 59 (.leaf 1125735334) (.leaf 1101344759))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1077564963) (.branch 62 (.leaf 1054376791) (.leaf 1031761858))) (.branch 65 (.branch 64 (.leaf 1009702505) (.leaf 988181770)) (.branch 66 (.leaf 967183350) (.leaf 946691576)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 926691377) (.leaf 907168255)) (.branch 70 (.leaf 888108259) (.leaf 869497958))) (.branch 73 (.branch 72 (.leaf 851324419) (.leaf 833575183)) (.branch 74 (.leaf 816238246) (.leaf 799302033))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 782755387) (.branch 77 (.leaf 766587543) (.leaf 750788117))) (.branch 80 (.branch 79 (.leaf 735347083) (.leaf 720254765)) (.branch 81 (.leaf 705501814) (.leaf 691079200)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 676978197) (.leaf 663190369)) (.branch 85 (.leaf 649707558) (.leaf 636521874))) (.branch 88 (.branch 87 (.leaf 623625683) (.leaf 611011596)) (.branch 89 (.leaf 598672460) (.leaf 586601350)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 574791555) (.branch 92 (.leaf 563236576) (.leaf 551930111))) (.branch 95 (.branch 94 (.leaf 540866053) (.leaf 530038480)) (.branch 96 (.leaf 519441647) (.leaf 509069981)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 498918075) (.leaf 488980679)) (.branch 100 (.leaf 479252696) (.leaf 469729177))) (.branch 103 (.branch 102 (.leaf 460405315) (.leaf 451276438)) (.branch 104 (.leaf 442338007) (.leaf 433585610))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 425014958) (.leaf 416621879)) (.branch 108 (.leaf 408402317) (.leaf 400352324))) (.branch 111 (.branch 110 (.leaf 392468061) (.leaf 384745789)) (.branch 112 (.leaf 377181871) (.leaf 369772765)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 362515022) (.leaf 355405282)) (.branch 116 (.leaf 348440273) (.leaf 341616808))) (.branch 119 (.branch 118 (.leaf 334931779) (.leaf 328382159)) (.branch 120 (.leaf 321964996) (.leaf 315677413)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 591).prefactor = (59022084377519/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 591).cutoff/(generalMeanRows 591).c)).2 =
    (25086687421333/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 591).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 591).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 591).q*(generalMeanRows 591).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 591).q*(generalMeanRows 591).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 591).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 591

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 591).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 591).criticalRate j.val*(generalMeanRows 591).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 591).c*(generalMeanRows 591).criticalPoint j.val)).2-
      (generalMeanRows 591).J/2-(generalMeanRows 591).error (generalMeanGrid j.val)+
      (generalMeanRows 591).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 591).c)).2-
      (generalMeanRows 591).J/2-(generalMeanRows 591).error 4 := by
  have he : (generalMeanRows 591).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 591) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 591)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0591

/-! Kernel-checked entropy margins for general spectral rectangle 592. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0592
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5105068016) (.branch 2 (.leaf 4929607956) (.leaf 4762036411))) (.branch 5 (.branch 4 (.leaf 4601902238) (.leaf 4448786192)) (.branch 6 (.leaf 4302298147) (.leaf 4162074610)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4027776497) (.leaf 3899087143)) (.branch 10 (.leaf 3775710498) (.leaf 3657369513))) (.branch 13 (.branch 12 (.leaf 3543804671) (.leaf 3434772655)) (.branch 14 (.leaf 3330045147) (.leaf 3229407721))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3132658841) (.branch 17 (.leaf 3039608950) (.leaf 2950079622))) (.branch 20 (.branch 19 (.leaf 2863902798) (.leaf 2780920079)) (.branch 21 (.leaf 2700982070) (.leaf 2623947789)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2549684109) (.leaf 2478065250)) (.branch 25 (.leaf 2408972307) (.leaf 2342292814))) (.branch 28 (.branch 27 (.leaf 2277920338) (.leaf 2215754106)) (.branch 29 (.leaf 2155698655) (.leaf 2097663509)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2041562875) (.branch 32 (.leaf 1987315369) (.leaf 1934843749))) (.branch 35 (.branch 34 (.leaf 1884074672) (.leaf 1834938468)) (.branch 36 (.leaf 1787368929) (.leaf 1741303107)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1696681132) (.leaf 1653446033)) (.branch 40 (.leaf 1611543584) (.leaf 1570922142))) (.branch 43 (.branch 42 (.leaf 1531532510) (.leaf 1493327804)) (.branch 44 (.leaf 1456263321) (.leaf 1420296427))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1385386445) (.branch 47 (.leaf 1351494547) (.leaf 1318583660))) (.branch 50 (.branch 49 (.leaf 1286618373) (.leaf 1255564849)) (.branch 51 (.leaf 1225390743) (.leaf 1196065128)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1167558420) (.leaf 1139842307)) (.branch 55 (.leaf 1112889693) (.leaf 1086674626))) (.branch 58 (.branch 57 (.leaf 1061172252) (.leaf 1036358750)) (.branch 59 (.leaf 1012211290) (.leaf 988707979))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 965827816) (.branch 62 (.leaf 943550652) (.leaf 921857146))) (.branch 65 (.branch 64 (.leaf 900728726) (.leaf 880147557)) (.branch 66 (.leaf 860096500) (.leaf 840559084)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 821519474) (.leaf 802962440)) (.branch 70 (.leaf 784873329) (.leaf 767238044))) (.branch 73 (.branch 72 (.leaf 750043009) (.leaf 733275157)) (.branch 74 (.leaf 716921897) (.leaf 700971099))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 685411072) (.branch 77 (.leaf 670230544) (.leaf 655418646))) (.branch 80 (.branch 79 (.leaf 640964890) (.leaf 626859159)) (.branch 81 (.leaf 613091684) (.leaf 599653036)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 586534107) (.leaf 573726098)) (.branch 85 (.leaf 561220508) (.leaf 549009119))) (.branch 88 (.branch 87 (.leaf 537083985) (.leaf 525437422)) (.branch 89 (.leaf 514061996) (.leaf 502950516)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 492096020) (.branch 92 (.leaf 481491768) (.leaf 471131235))) (.branch 95 (.branch 94 (.leaf 461008100) (.leaf 451116239)) (.branch 96 (.leaf 441449719) (.leaf 432002786)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 422769865) (.leaf 413745549)) (.branch 100 (.leaf 404924592) (.leaf 396301906))) (.branch 103 (.branch 102 (.leaf 387872553) (.leaf 379631741)) (.branch 104 (.leaf 371574817) (.leaf 363697266))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355994699) (.leaf 348462856)) (.branch 108 (.leaf 341097596) (.leaf 333894896))) (.branch 111 (.branch 110 (.leaf 326850846) (.leaf 319961646)) (.branch 112 (.leaf 313223599) (.leaf 306633112)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300186689) (.leaf 293880930)) (.branch 116 (.leaf 287712527) (.leaf 281678260))) (.branch 119 (.branch 118 (.leaf 275774996) (.leaf 269999686)) (.branch 120 (.leaf 264349359) (.leaf 258821125)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 592).prefactor = (2429651361608601/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 592).cutoff/(generalMeanRows 592).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 592).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 592).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 592).q*(generalMeanRows 592).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 592).q*(generalMeanRows 592).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 592).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 592

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 592).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 592).criticalRate j.val*(generalMeanRows 592).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 592).c*(generalMeanRows 592).criticalPoint j.val)).2-
      (generalMeanRows 592).J/2-(generalMeanRows 592).error (generalMeanGrid j.val)+
      (generalMeanRows 592).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 592).c)).2-
      (generalMeanRows 592).J/2-(generalMeanRows 592).error 4 := by
  have he : (generalMeanRows 592).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 592) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 592)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0592

/-! Kernel-checked entropy margins for general spectral rectangle 593. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0593
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5227274246) (.branch 2 (.leaf 5050114452) (.leaf 4880889204))) (.branch 5 (.branch 4 (.leaf 4719144414) (.leaf 4564458136)) (.branch 6 (.leaf 4416437754) (.leaf 4274717485)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4138956134) (.leaf 4008835087)) (.branch 10 (.leaf 3884056501) (.leaf 3764341668))) (.branch 13 (.branch 12 (.leaf 3649429537) (.leaf 3539075379)) (.branch 14 (.leaf 3433049565) (.leaf 3331136460))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3233133409) (.branch 17 (.leaf 3138849819) (.leaf 3048106306))) (.branch 20 (.branch 19 (.leaf 2960733924) (.leaf 2876573451)) (.branch 21 (.leaf 2795474733) (.leaf 2717296083)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2641903721) (.leaf 2569171263)) (.branch 25 (.leaf 2498979243) (.leaf 2431214675))) (.branch 28 (.branch 27 (.leaf 2365770647) (.leaf 2302545939)) (.branch 29 (.leaf 2241444674) (.leaf 2182375993)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2125253749) (.branch 32 (.leaf 2069996227) (.leaf 2016525878))) (.branch 35 (.branch 34 (.leaf 1964769078) (.leaf 1914655893)) (.branch 36 (.leaf 1866119869) (.leaf 1819097832)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1773529700) (.leaf 1729358309)) (.branch 40 (.leaf 1686529248) (.leaf 1644990704))) (.branch 43 (.branch 42 (.leaf 1604693325) (.leaf 1565590076)) (.branch 44 (.leaf 1527636119) (.leaf 1490788692))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1455006996) (.branch 47 (.leaf 1420252093) (.leaf 1386486804))) (.branch 50 (.branch 49 (.leaf 1353675620) (.leaf 1321784610)) (.branch 51 (.leaf 1290781343) (.leaf 1260634809)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1231315345) (.leaf 1202794568)) (.branch 55 (.leaf 1175045310) (.leaf 1148041553))) (.branch 58 (.branch 57 (.leaf 1121758379) (.leaf 1096171907)) (.branch 59 (.leaf 1071259247) (.leaf 1046998452))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1023368466) (.branch 62 (.leaf 1000349088) (.leaf 977920925))) (.branch 65 (.branch 64 (.leaf 956065359) (.leaf 934764503)) (.branch 66 (.leaf 914001174) (.leaf 893758853)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 874021661) (.leaf 854774323)) (.branch 70 (.leaf 836002143) (.leaf 817690978))) (.branch 73 (.branch 72 (.leaf 799827213) (.leaf 782397734)) (.branch 74 (.leaf 765389910) (.leaf 748791569))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 732590977) (.branch 77 (.leaf 716776821) (.leaf 701338187))) (.branch 80 (.branch 79 (.leaf 686264548) (.leaf 671545742)) (.branch 81 (.leaf 657171960) (.leaf 643133730)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 629421900) (.leaf 616027631)) (.branch 85 (.leaf 602942377) (.leaf 590157876))) (.branch 88 (.branch 87 (.leaf 577666140) (.leaf 565459441)) (.branch 89 (.leaf 553530302) (.leaf 541871487)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 530475989) (.branch 92 (.leaf 519337024) (.leaf 508448023))) (.branch 95 (.branch 94 (.leaf 497802618) (.leaf 487394642)) (.branch 96 (.leaf 477218114) (.leaf 467267236)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 457536386) (.leaf 448020110)) (.branch 100 (.leaf 438713117) (.leaf 429610272))) (.branch 103 (.branch 102 (.leaf 420706590) (.leaf 411997232)) (.branch 104 (.leaf 403477498) (.leaf 395142824))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 386988776) (.leaf 379011043)) (.branch 108 (.leaf 371205440) (.leaf 363567894))) (.branch 111 (.branch 110 (.leaf 356094448) (.leaf 348781252)) (.branch 112 (.leaf 341624563) (.leaf 334620739)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 327766236) (.leaf 321057605)) (.branch 116 (.leaf 314491490) (.leaf 308064623))) (.branch 119 (.branch 118 (.leaf 301773823) (.leaf 295615992)) (.branch 120 (.leaf 289588111) (.leaf 283687242)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 593).prefactor = (4892993294395183/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 593).cutoff/(generalMeanRows 593).c)).2 =
    (384677847606021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 593).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 593).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 593).q*(generalMeanRows 593).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 593).q*(generalMeanRows 593).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 593).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 593

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 593).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 593).criticalRate j.val*(generalMeanRows 593).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 593).c*(generalMeanRows 593).criticalPoint j.val)).2-
      (generalMeanRows 593).J/2-(generalMeanRows 593).error (generalMeanGrid j.val)+
      (generalMeanRows 593).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 593).c)).2-
      (generalMeanRows 593).J/2-(generalMeanRows 593).error 4 := by
  have he : (generalMeanRows 593).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 593) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 593)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0593

/-! Kernel-checked entropy margins for general spectral rectangle 594. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0594
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5296824626) (.branch 2 (.leaf 5124690611) (.leaf 4960187918))) (.branch 5 (.branch 4 (.leaf 4802877968) (.leaf 4652353355)) (.branch 6 (.leaf 4508235123) (.leaf 4370170340)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4237829915) (.leaf 4110906654)) (.branch 10 (.leaf 3989113495) (.leaf 3872181924))) (.branch 13 (.branch 12 (.leaf 3759860541) (.leaf 3651913755)) (.branch 14 (.leaf 3548120603) (.leaf 3448273675))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3352178127) (.branch 17 (.leaf 3259650787) (.leaf 3170519333))) (.branch 20 (.branch 19 (.leaf 3084621537) (.leaf 3001804575)) (.branch 21 (.leaf 2921924390) (.leaf 2844845103)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2770438479) (.leaf 2698583419)) (.branch 25 (.leaf 2629165507) (.leaf 2562076577))) (.branch 28 (.branch 27 (.leaf 2497214322) (.leaf 2434481921)) (.branch 29 (.leaf 2373787705) (.leaf 2315044838)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2258171020) (.branch 32 (.leaf 2203088216) (.leaf 2149722403))) (.branch 35 (.branch 34 (.leaf 2098003325) (.leaf 2047864278)) (.branch 36 (.leaf 1999241901) (.leaf 1952075979)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1906309266) (.leaf 1861887315)) (.branch 40 (.leaf 1818758319) (.leaf 1776872960))) (.branch 43 (.branch 42 (.leaf 1736184276) (.leaf 1696647525)) (.branch 44 (.leaf 1658220066) (.leaf 1620861242))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1584532274) (.branch 47 (.leaf 1549196159) (.leaf 1514817575))) (.branch 50 (.branch 49 (.leaf 1481362791) (.leaf 1448799585)) (.branch 51 (.leaf 1417097162) (.leaf 1386226079)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1356158179) (.leaf 1326866523)) (.branch 55 (.leaf 1298325323) (.leaf 1270509891))) (.branch 58 (.branch 57 (.leaf 1243396579) (.leaf 1216962726)) (.branch 59 (.leaf 1191186611) (.leaf 1166047406))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1141525132) (.branch 62 (.leaf 1117600615) (.leaf 1094255451))) (.branch 65 (.branch 64 (.leaf 1071471965) (.leaf 1049233179)) (.branch 66 (.leaf 1027522776) (.leaf 1006325069)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 985624975) (.leaf 965407982)) (.branch 70 (.leaf 945660125) (.leaf 926367960))) (.branch 73 (.branch 72 (.leaf 907518539) (.leaf 889099391)) (.branch 74 (.leaf 871098495) (.leaf 853504267))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 836305531) (.branch 77 (.leaf 819491511) (.leaf 803051805))) (.branch 80 (.branch 79 (.leaf 786976374) (.leaf 771255524)) (.branch 81 (.leaf 755879892) (.leaf 740840429)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 726128394) (.leaf 711735331)) (.branch 85 (.leaf 697653064) (.leaf 683873685))) (.branch 88 (.branch 87 (.leaf 670389539) (.leaf 657193218)) (.branch 89 (.leaf 644277547) (.leaf 631635580)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 619260585) (.branch 92 (.leaf 607146037) (.leaf 595285614))) (.branch 95 (.branch 94 (.leaf 583673184) (.leaf 572302801)) (.branch 96 (.leaf 561168694) (.leaf 550265265)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539587080) (.leaf 529128862)) (.branch 100 (.leaf 518885488) (.leaf 508851981))) (.branch 103 (.branch 102 (.leaf 499023503) (.leaf 489395355)) (.branch 104 (.leaf 479962969) (.leaf 470721903))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 461667836) (.leaf 452796566)) (.branch 108 (.leaf 444104006) (.leaf 435586176))) (.branch 111 (.branch 110 (.leaf 427239204) (.leaf 419059320)) (.branch 112 (.leaf 411042853) (.leaf 403186227)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 395485960) (.leaf 387938659)) (.branch 116 (.leaf 380541017) (.leaf 373289812))) (.branch 119 (.branch 118 (.leaf 366181901) (.leaf 359214223)) (.branch 120 (.leaf 352383789) (.leaf 345687688)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 594).prefactor = (4753911785518663/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 594).cutoff/(generalMeanRows 594).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 594).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 594).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 594).q*(generalMeanRows 594).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 594).q*(generalMeanRows 594).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 594).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 594

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 594).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 594).criticalRate j.val*(generalMeanRows 594).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 594).c*(generalMeanRows 594).criticalPoint j.val)).2-
      (generalMeanRows 594).J/2-(generalMeanRows 594).error (generalMeanGrid j.val)+
      (generalMeanRows 594).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 594).c)).2-
      (generalMeanRows 594).J/2-(generalMeanRows 594).error 4 := by
  have he : (generalMeanRows 594).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 594) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 594)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0594

/-! Kernel-checked entropy margins for general spectral rectangle 595. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0595
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5424441100) (.branch 2 (.leaf 5250800325) (.leaf 5084832275))) (.branch 5 (.branch 4 (.leaf 4926095481) (.leaf 4774179883)) (.branch 6 (.leaf 4628704087) (.leaf 4489312915)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4355675212) (.leaf 4227481881)) (.branch 10 (.leaf 4104444109) (.leaf 3986291768))) (.branch 13 (.branch 12 (.leaf 3872771968) (.leaf 3763647747)) (.branch 14 (.leaf 3658696876) (.leaf 3557710777))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3460493531) (.branch 17 (.leaf 3366860975) (.leaf 3276639870))) (.branch 20 (.branch 19 (.leaf 3189667144) (.leaf 3105789196)) (.branch 21 (.leaf 3024861252) (.leaf 2946746773)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2871316914) (.leaf 2798450020)) (.branch 25 (.leaf 2728031156) (.leaf 2659951684))) (.branch 28 (.branch 27 (.leaf 2594108860) (.leaf 2530405465)) (.branch 29 (.leaf 2468749462) (.leaf 2409053675)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2351235499) (.branch 32 (.leaf 2295216614) (.leaf 2240922738))) (.branch 35 (.branch 34 (.leaf 2188283378) (.leaf 2137231616)) (.branch 36 (.leaf 2087703890) (.leaf 2039639808)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1992981960) (.leaf 1947675750)) (.branch 40 (.leaf 1903669235) (.leaf 1860912977))) (.branch 43 (.branch 42 (.leaf 1819359901) (.leaf 1778965166)) (.branch 44 (.leaf 1739686040) (.leaf 1701481786))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1664313552) (.branch 47 (.leaf 1628144269) (.leaf 1592938557))) (.branch 50 (.branch 49 (.leaf 1558662634) (.leaf 1525284229)) (.branch 51 (.leaf 1492772508) (.leaf 1461097991)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1430232490) (.leaf 1400149035)) (.branch 55 (.leaf 1370821816) (.leaf 1342226121))) (.branch 58 (.branch 57 (.leaf 1314338284) (.leaf 1287135628)) (.branch 59 (.leaf 1260596418) (.leaf 1234699813))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1209425822) (.branch 62 (.leaf 1184755264) (.leaf 1160669725))) (.branch 65 (.branch 64 (.leaf 1137151524) (.leaf 1114183677)) (.branch 66 (.leaf 1091749860) (.leaf 1069834383)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1048422158) (.leaf 1027498668)) (.branch 70 (.leaf 1007049944) (.leaf 987062537))) (.branch 73 (.branch 72 (.leaf 967523498) (.leaf 948420349)) (.branch 74 (.leaf 929741066) (.leaf 911474059))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 893608149) (.branch 77 (.leaf 876132552) (.leaf 859036862))) (.branch 80 (.branch 79 (.leaf 842311033) (.leaf 825945365)) (.branch 81 (.leaf 809930486) (.leaf 794257341)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 778917178) (.leaf 763901532)) (.branch 85 (.leaf 749202220) (.leaf 734811319))) (.branch 88 (.branch 87 (.leaf 720721166) (.leaf 706924338)) (.branch 89 (.leaf 693413651) (.leaf 680182142)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 667223065) (.branch 92 (.leaf 654529882) (.leaf 642096255))) (.branch 95 (.branch 94 (.leaf 629916034) (.leaf 617983256)) (.branch 96 (.leaf 606292135) (.leaf 594837051)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 583612553) (.leaf 572613344)) (.branch 100 (.leaf 561834278) (.leaf 551270359))) (.branch 103 (.branch 102 (.leaf 540916728) (.leaf 530768662)) (.branch 104 (.leaf 520821570) (.leaf 511070986))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 501512566) (.leaf 492142082)) (.branch 108 (.leaf 482955422) (.leaf 473948580))) (.branch 111 (.branch 110 (.leaf 465117658) (.leaf 456458858)) (.branch 112 (.leaf 447968483) (.leaf 439642928)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 431478683) (.leaf 423472326)) (.branch 116 (.leaf 415620520) (.leaf 407920014))) (.branch 119 (.branch 118 (.leaf 400367636) (.leaf 392960293)) (.branch 120 (.leaf 385694967) (.leaf 378568713)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 595).prefactor = (4786275659111853/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 595).cutoff/(generalMeanRows 595).c)).2 =
    (208356484609779/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 595).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 595).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 595).q*(generalMeanRows 595).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 595).q*(generalMeanRows 595).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 595).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 595

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 595).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 595).criticalRate j.val*(generalMeanRows 595).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 595).c*(generalMeanRows 595).criticalPoint j.val)).2-
      (generalMeanRows 595).J/2-(generalMeanRows 595).error (generalMeanGrid j.val)+
      (generalMeanRows 595).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 595).c)).2-
      (generalMeanRows 595).J/2-(generalMeanRows 595).error 4 := by
  have he : (generalMeanRows 595).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 595) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 595)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0595

/-! Kernel-checked entropy margins for general spectral rectangle 596. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0596
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5130130847) (.branch 2 (.leaf 4960940149) (.leaf 4799269539))) (.branch 5 (.branch 4 (.leaf 4644687770) (.leaf 4496794199)) (.branch 6 (.leaf 4355216109) (.leaf 4219606332)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4089641109) (.leaf 3965018173)) (.branch 10 (.leaf 3845455028) (.leaf 3730687390))) (.branch 13 (.branch 12 (.leaf 3620467775) (.leaf 3514564231)) (.branch 14 (.leaf 3412759166) (.leaf 3314848303))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3220639707) (.branch 17 (.leaf 3129952909) (.leaf 3042618100))) (.branch 20 (.branch 19 (.leaf 2958475389) (.leaf 2877374124)) (.branch 21 (.leaf 2799172271) (.leaf 2723735835)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2650938333) (.leaf 2580660301)) (.branch 25 (.leaf 2512788842) (.leaf 2447217210))) (.branch 28 (.branch 27 (.leaf 2383844418) (.leaf 2322574879)) (.branch 29 (.leaf 2263318074) (.leaf 2205988237)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2150504072) (.branch 32 (.leaf 2096788477) (.leaf 2044768300))) (.branch 35 (.branch 34 (.leaf 1994374103) (.leaf 1945539942)) (.branch 36 (.leaf 1898203167) (.leaf 1852304229)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1807786505) (.leaf 1764596129)) (.branch 40 (.leaf 1722681839) (.leaf 1681994829))) (.branch 43 (.branch 42 (.leaf 1642488613) (.leaf 1604118899)) (.branch 44 (.leaf 1566843464) (.leaf 1530622046))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1495416236) (.branch 47 (.leaf 1461189380) (.leaf 1427906480))) (.branch 50 (.branch 49 (.leaf 1395534115) (.leaf 1364040351)) (.branch 51 (.leaf 1333394664) (.leaf 1303567870)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1274532055) (.leaf 1246260505)) (.branch 55 (.leaf 1218727653) (.leaf 1191909014))) (.branch 58 (.branch 57 (.leaf 1165781133) (.leaf 1140321534)) (.branch 59 (.leaf 1115508671) (.leaf 1091321883))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1067741347) (.branch 62 (.leaf 1044748041) (.leaf 1022323705))) (.branch 65 (.branch 64 (.leaf 1000450802) (.leaf 979112484)) (.branch 66 (.leaf 958292561) (.leaf 937975469)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 918146239) (.leaf 898790473)) (.branch 70 (.leaf 879894312) (.leaf 861444418))) (.branch 73 (.branch 72 (.leaf 843427945) (.leaf 825832518)) (.branch 74 (.leaf 808646212) (.leaf 791857535))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 775455402) (.branch 77 (.leaf 759429122) (.leaf 743768381))) (.branch 80 (.branch 79 (.leaf 728463223) (.leaf 713504034)) (.branch 81 (.leaf 698881533) (.leaf 684586750)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 670611018) (.leaf 656945959)) (.branch 85 (.leaf 643583472) (.leaf 630515722))) (.branch 88 (.branch 87 (.leaf 617735126) (.leaf 605234349)) (.branch 89 (.leaf 593006286) (.leaf 581044059)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 569341007) (.branch 92 (.leaf 557890675) (.leaf 546686807))) (.branch 95 (.branch 94 (.leaf 535723338) (.leaf 524994388)) (.branch 96 (.leaf 514494255) (.leaf 504217405)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 494158470) (.leaf 484312237)) (.branch 100 (.leaf 474673648) (.leaf 465237789))) (.branch 103 (.branch 102 (.leaf 455999888) (.leaf 446955309)) (.branch 104 (.leaf 438099546) (.leaf 429428220))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 420937073) (.leaf 412621966)) (.branch 108 (.leaf 404478872) (.leaf 396503875))) (.branch 111 (.branch 110 (.leaf 388693163) (.leaf 381043027)) (.branch 112 (.leaf 373549858) (.leaf 366210140)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 359020452) (.leaf 351977461)) (.branch 116 (.leaf 345077920) (.leaf 338318665))) (.branch 119 (.branch 118 (.leaf 331696616) (.leaf 325208767)) (.branch 120 (.leaf 318852192) (.leaf 312624036)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 596).prefactor = (467536464812103/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 596).cutoff/(generalMeanRows 596).c)).2 =
    (399951248315223/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 596).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 596).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 596).q*(generalMeanRows 596).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 596).q*(generalMeanRows 596).cutoff/2-2 = (16250/7667:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable207.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 596).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 596

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 596).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 596).criticalRate j.val*(generalMeanRows 596).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 596).c*(generalMeanRows 596).criticalPoint j.val)).2-
      (generalMeanRows 596).J/2-(generalMeanRows 596).error (generalMeanGrid j.val)+
      (generalMeanRows 596).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 596).c)).2-
      (generalMeanRows 596).J/2-(generalMeanRows 596).error 4 := by
  have he : (generalMeanRows 596).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 596) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 596)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0596

/-! Kernel-checked entropy margins for general spectral rectangle 597. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0597
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5138875446) (.branch 2 (.leaf 4969396354) (.leaf 4807450167))) (.branch 5 (.branch 4 (.leaf 4652604905) (.leaf 4504459240)) (.branch 6 (.leaf 4362639822) (.leaf 4226798891)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4096612135) (.leaf 3971776772)) (.branch 10 (.leaf 3852009825) (.leaf 3737046558))) (.branch 13 (.branch 12 (.leaf 3626639068) (.leaf 3520555005)) (.branch 14 (.leaf 3418576408) (.leaf 3320498650))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3226129470) (.branch 17 (.leaf 3135288092) (.leaf 3047804416))) (.branch 20 (.branch 19 (.leaf 2963518278) (.leaf 2882278771)) (.branch 21 (.leaf 2803943619) (.leaf 2728378598)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2655457008) (.leaf 2585059183)) (.branch 25 (.leaf 2517072034) (.leaf 2451388631))) (.branch 28 (.branch 27 (.leaf 2387907816) (.leaf 2326533840)) (.branch 29 (.leaf 2267176028) (.leaf 2209748470)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2154169728) (.branch 32 (.leaf 2100362572) (.leaf 2048253724))) (.branch 35 (.branch 34 (.leaf 1997773627) (.leaf 1948856225)) (.branch 36 (.leaf 1901438762) (.leaf 1855461587)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1810867980) (.leaf 1767603983)) (.branch 40 (.leaf 1725618248) (.leaf 1684861885))) (.branch 43 (.branch 42 (.leaf 1645288329) (.leaf 1606853211)) (.branch 44 (.leaf 1569514237) (.leaf 1533231078))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1497965258) (.branch 47 (.leaf 1463680060) (.leaf 1430340428))) (.branch 50 (.branch 49 (.leaf 1397912883) (.leaf 1366365435)) (.branch 51 (.leaf 1335667511) (.leaf 1305789876)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1276704567) (.leaf 1248384827)) (.branch 55 (.leaf 1220805044) (.leaf 1193940691))) (.branch 58 (.branch 57 (.leaf 1167768273) (.leaf 1142265277)) (.branch 59 (.leaf 1117410119) (.leaf 1093182103))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1069561373) (.branch 62 (.leaf 1046528874) (.leaf 1024066314))) (.branch 65 (.branch 64 (.leaf 1002156127) (.leaf 980781437)) (.branch 66 (.leaf 959926025) (.leaf 939574302)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 919711272) (.leaf 900322512)) (.branch 70 (.leaf 881394142) (.leaf 862912799))) (.branch 73 (.branch 72 (.leaf 844865616) (.leaf 827240196)) (.branch 74 (.leaf 810024596) (.leaf 793207301))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 776777210) (.branch 77 (.leaf 760723612) (.leaf 745036177))) (.branch 80 (.branch 79 (.leaf 729704930) (.leaf 714720243)) (.branch 81 (.leaf 700072816) (.leaf 685753667)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 671754112) (.leaf 658065761)) (.branch 85 (.leaf 644680497) (.leaf 631590472))) (.branch 88 (.branch 87 (.leaf 618788091) (.leaf 606266005)) (.branch 89 (.leaf 594017099) (.leaf 582034482)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 570311482) (.branch 92 (.leaf 558841631) (.leaf 547618665))) (.branch 95 (.branch 94 (.leaf 536636509) (.leaf 525889271)) (.branch 96 (.leaf 515371240) (.leaf 505076872)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 495000791) (.leaf 485137775)) (.branch 100 (.leaf 475482756) (.leaf 466030813))) (.branch 103 (.branch 102 (.leaf 456777166) (.leaf 447717170)) (.branch 104 (.leaf 438846312) (.leaf 430160205))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 421654584) (.leaf 413325304)) (.branch 108 (.leaf 405168329) (.leaf 397179738))) (.branch 111 (.branch 110 (.leaf 389355712) (.leaf 381692536)) (.branch 112 (.leaf 374186595) (.leaf 366834366)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 359632423) (.leaf 352577426)) (.branch 116 (.leaf 345666125) (.leaf 338895349))) (.branch 119 (.branch 118 (.leaf 332262012) (.leaf 325763104)) (.branch 120 (.leaf 319395694) (.leaf 313156922)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 597).prefactor = (2341667036422991/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 597).cutoff/(generalMeanRows 597).c)).2 =
    (399951248315223/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 597).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 597).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 597).q*(generalMeanRows 597).c/2-2 = (1523/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable169.value]
    have hcontinuation : (generalMeanRows 597).q*(generalMeanRows 597).cutoff/2-2 = (16250/7667:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable207.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 597).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 597

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 597).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 597).criticalRate j.val*(generalMeanRows 597).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 597).c*(generalMeanRows 597).criticalPoint j.val)).2-
      (generalMeanRows 597).J/2-(generalMeanRows 597).error (generalMeanGrid j.val)+
      (generalMeanRows 597).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 597).c)).2-
      (generalMeanRows 597).J/2-(generalMeanRows 597).error 4 := by
  have he : (generalMeanRows 597).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 597) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 597)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0597

/-! Kernel-checked entropy margins for general spectral rectangle 598. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0598
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5062977369) (.branch 2 (.leaf 4893583218) (.leaf 4731738652))) (.branch 5 (.branch 4 (.leaf 4577011614) (.leaf 4429000658)) (.branch 6 (.leaf 4287332273) (.leaf 4151658504)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4021654809) (.leaf 3897018151)) (.branch 10 (.leaf 3777465271) (.leaf 3662731128))) (.branch 13 (.branch 12 (.leaf 3552567496) (.leaf 3446741682)) (.branch 14 (.leaf 3345035374) (.leaf 3247243575))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3153173648) (.branch 17 (.leaf 3062644430) (.leaf 2975485430))) (.branch 20 (.branch 19 (.leaf 2891536085) (.leaf 2810645087)) (.branch 21 (.leaf 2732669754) (.leaf 2657475459)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2584935096) (.leaf 2514928593)) (.branch 25 (.leaf 2447342458) (.leaf 2382069360))) (.branch 28 (.branch 27 (.leaf 2319007742) (.leaf 2258061462)) (.branch 29 (.leaf 2199139453) (.leaf 2142155421)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2087027549) (.branch 32 (.leaf 2033678231) (.leaf 1982033820))) (.branch 35 (.branch 34 (.leaf 1932024399) (.leaf 1883583556)) (.branch 36 (.leaf 1836648184) (.leaf 1791158293)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1747056828) (.leaf 1704289504)) (.branch 40 (.leaf 1662804651) (.leaf 1622553069))) (.branch 43 (.branch 42 (.leaf 1583487888) (.leaf 1545564442)) (.branch 44 (.leaf 1508740148) (.leaf 1472974393))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1438228429) (.branch 47 (.leaf 1404465272) (.leaf 1371649606))) (.branch 50 (.branch 49 (.leaf 1339747700) (.leaf 1308727322)) (.branch 51 (.leaf 1278557661) (.leaf 1249209252)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1220653911) (.leaf 1192864664)) (.branch 55 (.leaf 1165815692) (.leaf 1139482266))) (.branch 58 (.branch 57 (.leaf 1113840698) (.leaf 1088868285)) (.branch 59 (.leaf 1064543263) (.leaf 1040844759))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1017752751) (.branch 62 (.leaf 995248021) (.leaf 973312120))) (.branch 65 (.branch 64 (.leaf 951927331) (.leaf 931076633)) (.branch 66 (.leaf 910743671) (.leaf 890912718)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 871568654) (.leaf 852696932)) (.branch 70 (.leaf 834283553) (.leaf 816315042))) (.branch 73 (.branch 72 (.leaf 798778424) (.leaf 781661201)) (.branch 74 (.leaf 764951330) (.leaf 748637203))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 732707628) (.branch 77 (.leaf 717151811) (.leaf 701959340))) (.branch 80 (.branch 79 (.leaf 687120163) (.leaf 672624580)) (.branch 81 (.leaf 658463223) (.leaf 644627041)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 631107291) (.leaf 617895524)) (.branch 85 (.leaf 604983568) (.leaf 592363524))) (.branch 88 (.branch 87 (.leaf 580027749) (.leaf 567968847)) (.branch 89 (.leaf 556179662) (.leaf 544653264)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 533382943) (.branch 92 (.leaf 522362199) (.leaf 511584735))) (.branch 95 (.branch 94 (.leaf 501044447) (.leaf 490735420)) (.branch 96 (.leaf 480651916) (.leaf 470788371)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 461139388) (.leaf 451699730)) (.branch 100 (.leaf 442464314) (.leaf 433428204))) (.branch 103 (.branch 102 (.leaf 424586609) (.leaf 415934876)) (.branch 104 (.leaf 407468483) (.leaf 399183039))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 391074275) (.leaf 383138040)) (.branch 108 (.leaf 375370302) (.leaf 367767136))) (.branch 111 (.branch 110 (.leaf 360324727) (.leaf 353039364)) (.branch 112 (.leaf 345907434) (.leaf 338925423)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332089910) (.leaf 325397564)) (.branch 116 (.leaf 318845143) (.leaf 312429488))) (.branch 119 (.branch 118 (.leaf 306147524) (.leaf 299996255)) (.branch 120 (.leaf 293972760) (.leaf 288074194)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 598).prefactor = (36599829454971/7812500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 598).cutoff/(generalMeanRows 598).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 598).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 598).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 598).q*(generalMeanRows 598).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 598).q*(generalMeanRows 598).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 598).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 598

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 598).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 598).criticalRate j.val*(generalMeanRows 598).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 598).c*(generalMeanRows 598).criticalPoint j.val)).2-
      (generalMeanRows 598).J/2-(generalMeanRows 598).error (generalMeanGrid j.val)+
      (generalMeanRows 598).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 598).c)).2-
      (generalMeanRows 598).J/2-(generalMeanRows 598).error 4 := by
  have he : (generalMeanRows 598).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 598) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 598)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0598

/-! Kernel-checked entropy margins for general spectral rectangle 599. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0599
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5071642805) (.branch 2 (.leaf 4901958731) (.leaf 4739837163))) (.branch 5 (.branch 4 (.leaf 4584845305) (.leaf 4436581024)) (.branch 6 (.leaf 4294670170) (.leaf 4158764190)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4028537990) (.leaf 3903688014)) (.branch 10 (.leaf 3783930515) (.leaf 3669000001))) (.branch 13 (.branch 12 (.leaf 3558647820) (.leaf 3452640883)) (.branch 14 (.leaf 3350760501) (.leaf 3252801329))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3158570399) (.branch 17 (.leaf 3067886237) (.leaf 2980578061))) (.branch 20 (.branch 19 (.leaf 2896485035) (.leaf 2815455589)) (.branch 21 (.leaf 2737346800) (.leaf 2662023808)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2589359290) (.leaf 2519232968)) (.branch 25 (.leaf 2451531157) (.leaf 2386146342))) (.branch 28 (.branch 27 (.leaf 2322976793) (.leaf 2261926201)) (.branch 29 (.leaf 2202903346) (.leaf 2145821784)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2090599559) (.branch 32 (.leaf 2037158931) (.leaf 1985426130))) (.branch 35 (.branch 34 (.leaf 1935331116) (.leaf 1886807365)) (.branch 36 (.leaf 1839791662) (.leaf 1794223914)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1750046967) (.leaf 1707206446)) (.branch 40 (.leaf 1665650591) (.leaf 1625330117))) (.branch 43 (.branch 42 (.leaf 1586198075) (.leaf 1548209721)) (.branch 44 (.leaf 1511322402) (.leaf 1475495433))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1440690000) (.branch 47 (.leaf 1406869056) (.leaf 1373997225))) (.branch 50 (.branch 49 (.leaf 1342040718) (.leaf 1310967248)) (.branch 51 (.leaf 1280745950) (.leaf 1251347311)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1222743096) (.leaf 1194906288)) (.branch 55 (.leaf 1167811020) (.leaf 1141432524))) (.branch 58 (.branch 57 (.leaf 1115747069) (.leaf 1090731915)) (.branch 59 (.leaf 1066365260) (.leaf 1042626196))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1019494665) (.branch 62 (.leaf 996951417) (.leaf 974977972))) (.branch 65 (.branch 64 (.leaf 953556583) (.leaf 932670199)) (.branch 66 (.leaf 912302436) (.leaf 892437542)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 873060370) (.leaf 854156348)) (.branch 70 (.leaf 835711454) (.leaf 817712189))) (.branch 73 (.branch 72 (.leaf 800145557) (.leaf 782999038)) (.branch 74 (.leaf 766260567) (.leaf 749918518))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 733961679) (.branch 77 (.leaf 718379238) (.leaf 703160764))) (.branch 80 (.branch 79 (.leaf 688296190) (.leaf 673775797)) (.branch 81 (.leaf 659590202) (.leaf 645730339)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 632187450) (.leaf 618953070)) (.branch 85 (.leaf 606019016) (.leaf 593377372))) (.branch 88 (.branch 87 (.leaf 581020484) (.leaf 568940943)) (.branch 89 (.leaf 557131580) (.leaf 545585454)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534295843) (.branch 92 (.leaf 523256237) (.leaf 512460327))) (.branch 95 (.branch 94 (.leaf 501902000) (.leaf 491575328)) (.branch 96 (.leaf 481474566) (.leaf 471594139)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 461928642) (.leaf 452472828)) (.branch 100 (.leaf 443221605) (.leaf 434170029))) (.branch 103 (.branch 102 (.leaf 425313302) (.leaf 416646761)) (.branch 104 (.leaf 408165878) (.leaf 399866253))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 391743610) (.leaf 383793792)) (.branch 108 (.leaf 376012759) (.leaf 368396580))) (.branch 111 (.branch 110 (.leaf 360941434) (.leaf 353643601)) (.branch 112 (.leaf 346499465) (.leaf 339505504)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332658291) (.leaf 325954492)) (.branch 116 (.leaf 319390856) (.leaf 312964221))) (.branch 119 (.branch 118 (.leaf 306671505) (.leaf 300509707)) (.branch 120 (.leaf 294475903) (.leaf 288567242)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 599).prefactor = (4692796307142657/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 599).cutoff/(generalMeanRows 599).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 599).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 599).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 599).q*(generalMeanRows 599).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 599).q*(generalMeanRows 599).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 599).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 599

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 599).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 599).criticalRate j.val*(generalMeanRows 599).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 599).c*(generalMeanRows 599).criticalPoint j.val)).2-
      (generalMeanRows 599).J/2-(generalMeanRows 599).error (generalMeanGrid j.val)+
      (generalMeanRows 599).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 599).c)).2-
      (generalMeanRows 599).J/2-(generalMeanRows 599).error 4 := by
  have he : (generalMeanRows 599).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 599) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 599)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0599

/-! Kernel-checked entropy margins for general spectral rectangle 600. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0600
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5089018196) (.branch 2 (.leaf 4918752786) (.leaf 4756075791))) (.branch 5 (.branch 4 (.leaf 4600552933) (.leaf 4451780700)) (.branch 6 (.leaf 4309383661) (.leaf 4173012070)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4042339716) (.leaf 3917062005)) (.branch 10 (.leaf 3796894218) (.leaf 3681569954))) (.branch 13 (.branch 12 (.leaf 3570839707) (.leaf 3464469592)) (.branch 14 (.leaf 3362240169) (.leaf 3263945390))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3169391625) (.branch 17 (.leaf 3078396781) (.leaf 2990789488))) (.branch 20 (.branch 19 (.leaf 2906408360) (.leaf 2825101308)) (.branch 21 (.leaf 2746724919) (.leaf 2671143871)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2598230405) (.leaf 2527863832)) (.branch 25 (.leaf 2459930075) (.leaf 2394321253))) (.branch 28 (.branch 27 (.leaf 2330935285) (.leaf 2269675535)) (.branch 29 (.leaf 2210450468) (.leaf 2153173345)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2097761929) (.branch 32 (.leaf 2044138215) (.leaf 1992228178))) (.branch 35 (.branch 34 (.leaf 1941961539) (.leaf 1893271546)) (.branch 36 (.leaf 1846094767) (.leaf 1800370904)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1756042608) (.leaf 1713055316)) (.branch 40 (.leaf 1671357091) (.leaf 1630898480))) (.branch 43 (.branch 42 (.leaf 1591632371) (.leaf 1553513870)) (.branch 44 (.leaf 1516500175) (.leaf 1480550463))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1445625788) (.branch 47 (.leaf 1411688973) (.leaf 1378704524))) (.branch 50 (.branch 49 (.leaf 1346638534) (.leaf 1315458607)) (.branch 51 (.leaf 1285133771) (.leaf 1255634412)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1226932200) (.leaf 1199000023)) (.branch 55 (.leaf 1171811928) (.leaf 1145343059))) (.branch 58 (.branch 57 (.leaf 1119569606) (.leaf 1094468750)) (.branch 59 (.leaf 1070018615) (.leaf 1046198222))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1022987442) (.branch 62 (.leaf 1000366961) (.leaf 978318236))) (.branch 65 (.branch 64 (.leaf 956823457) (.leaf 935865516)) (.branch 66 (.leaf 915427974) (.leaf 895495023)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 876051465) (.leaf 857082678)) (.branch 70 (.leaf 838574592) (.leaf 820513662))) (.branch 73 (.branch 72 (.leaf 802886847) (.leaf 785681584)) (.branch 74 (.leaf 768885767) (.leaf 752487730))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 736476223) (.branch 77 (.leaf 720840397) (.leaf 705569785))) (.branch 80 (.branch 79 (.leaf 690654285) (.leaf 676084146)) (.branch 81 (.leaf 661849951) (.leaf 647942604)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 634353317) (.leaf 621073597)) (.branch 85 (.leaf 608095230) (.leaf 595410276))) (.branch 88 (.branch 87 (.leaf 583011053) (.leaf 570890128)) (.branch 89 (.leaf 559040306) (.leaf 547454624)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 536126335) (.branch 92 (.leaf 525048907) (.leaf 514216011))) (.branch 95 (.branch 94 (.leaf 503621510) (.leaf 493259460)) (.branch 96 (.leaf 483124092) (.leaf 473209815)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 463511204) (.leaf 454022995)) (.branch 100 (.leaf 444740077) (.leaf 435657491))) (.branch 103 (.branch 102 (.leaf 426770420) (.leaf 418074188)) (.branch 104 (.leaf 409564250) (.leaf 401236190))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 393085719) (.leaf 385108666)) (.branch 108 (.leaf 377300975) (.leaf 369658703))) (.branch 111 (.branch 110 (.leaf 362178015) (.leaf 354855180)) (.branch 112 (.leaf 347686568) (.leaf 340668646)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333797975) (.leaf 327071208)) (.branch 116 (.leaf 320485085) (.leaf 314036433))) (.branch 119 (.branch 118 (.leaf 307722158) (.leaf 301539250)) (.branch 120 (.leaf 295484774) (.leaf 289555870)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 600).prefactor = (588609221785151/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 600).cutoff/(generalMeanRows 600).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 600).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 600).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 600).q*(generalMeanRows 600).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 600).q*(generalMeanRows 600).cutoff/2-2 = (8114/3839:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable202.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 600).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 600

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 600).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 600).criticalRate j.val*(generalMeanRows 600).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 600).c*(generalMeanRows 600).criticalPoint j.val)).2-
      (generalMeanRows 600).J/2-(generalMeanRows 600).error (generalMeanGrid j.val)+
      (generalMeanRows 600).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 600).c)).2-
      (generalMeanRows 600).J/2-(generalMeanRows 600).error 4 := by
  have he : (generalMeanRows 600).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 600) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 600)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0600

/-! Kernel-checked entropy margins for general spectral rectangle 601. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0601
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5081594046) (.branch 2 (.leaf 4911592427) (.leaf 4749160566))) (.branch 5 (.branch 4 (.leaf 4593865745) (.leaf 4445305880)) (.branch 6 (.leaf 4303106849) (.leaf 4166920106)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4036420540) (.leaf 3911304563)) (.branch 10 (.leaf 3791288382) (.leaf 3676106440))) (.branch 13 (.branch 12 (.leaf 3565510011) (.leaf 3459265920)) (.branch 14 (.leaf 3357155380) (.leaf 3258972941))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3164525523) (.branch 17 (.leaf 3073631534) (.leaf 2986120065))) (.branch 20 (.branch 19 (.leaf 2901830151) (.leaf 2820610090)) (.branch 21 (.leaf 2742316821) (.leaf 2666815347)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2593978203) (.leaf 2523684969)) (.branch 25 (.leaf 2455821819) (.leaf 2390281093))) (.branch 28 (.branch 27 (.leaf 2326960919) (.leaf 2265764846)) (.branch 29 (.leaf 2206601512) (.leaf 2149384334)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2094031214) (.branch 32 (.leaf 2040464278) (.leaf 1988609619))) (.branch 35 (.branch 34 (.leaf 1938397062) (.leaf 1889759952)) (.branch 36 (.leaf 1842634946) (.leaf 1796961824)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1752683307) (.leaf 1709744897)) (.branch 40 (.leaf 1668094717) (.leaf 1627683364))) (.branch 43 (.branch 42 (.leaf 1588463776) (.leaf 1550391098)) (.branch 44 (.leaf 1513422567) (.leaf 1477517395))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1442636663) (.branch 47 (.leaf 1408743225) (.leaf 1375801609))) (.branch 50 (.branch 49 (.leaf 1343777930) (.leaf 1312639809)) (.branch 51 (.leaf 1282356292) (.leaf 1252897780)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1224235954) (.leaf 1196343715)) (.branch 55 (.leaf 1169195118) (.leaf 1142765318))) (.branch 58 (.branch 57 (.leaf 1117030511) (.leaf 1091967885)) (.branch 59 (.leaf 1067555568) (.leaf 1043772585))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1020598815) (.branch 62 (.leaf 998014944) (.leaf 976002431))) (.branch 65 (.branch 64 (.leaf 954543472) (.leaf 933620959)) (.branch 66 (.leaf 913218453) (.leaf 893320151)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 873910854) (.leaf 854975941)) (.branch 70 (.leaf 836501343) (.leaf 818473517))) (.branch 73 (.branch 72 (.leaf 800879421) (.leaf 783706493)) (.branch 74 (.leaf 766942628) (.leaf 750576161))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734595842) (.branch 77 (.leaf 718990823) (.leaf 703750636))) (.branch 80 (.branch 79 (.leaf 688865182) (.leaf 674324710)) (.branch 81 (.leaf 660119804) (.leaf 646241369)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 632680619) (.leaf 619429059)) (.branch 85 (.leaf 606478480) (.leaf 593820942))) (.branch 88 (.branch 87 (.leaf 581448763) (.leaf 569354513)) (.branch 89 (.leaf 557530999) (.leaf 545971259)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534668548) (.branch 92 (.leaf 523616337) (.leaf 512808297))) (.branch 95 (.branch 94 (.leaf 502238296) (.leaf 491900389)) (.branch 96 (.leaf 481788813) (.leaf 471897977)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 462222458) (.leaf 452756996)) (.branch 100 (.leaf 443496483) (.leaf 434435962))) (.branch 103 (.branch 102 (.leaf 425570620) (.leaf 416895781)) (.branch 104 (.leaf 408406906) (.leaf 400099582))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 391969522) (.leaf 384012557)) (.branch 108 (.leaf 376224636) (.leaf 368601819))) (.branch 111 (.branch 110 (.leaf 361140274) (.leaf 353836274)) (.branch 112 (.leaf 346686191) (.leaf 339686496)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332833755) (.leaf 326124622)) (.branch 116 (.leaf 319555841) (.leaf 313124243))) (.branch 119 (.branch 118 (.leaf 306826739) (.leaf 300660320)) (.branch 120 (.leaf 294622056) (.leaf 288709090)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 601).prefactor = (4694276870953671/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 601).cutoff/(generalMeanRows 601).c)).2 =
    (9737753075837/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 601).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 601).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 601).q*(generalMeanRows 601).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 601).q*(generalMeanRows 601).cutoff/2-2 = (5402/2563:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable208.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 601).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 601

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 601).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 601).criticalRate j.val*(generalMeanRows 601).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 601).c*(generalMeanRows 601).criticalPoint j.val)).2-
      (generalMeanRows 601).J/2-(generalMeanRows 601).error (generalMeanGrid j.val)+
      (generalMeanRows 601).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 601).c)).2-
      (generalMeanRows 601).J/2-(generalMeanRows 601).error 4 := by
  have he : (generalMeanRows 601).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 601) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 601)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0601

/-! Kernel-checked entropy margins for general spectral rectangle 602. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0602
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5090327027) (.branch 2 (.leaf 4920033252) (.leaf 4757322243))) (.branch 5 (.branch 4 (.leaf 4601760539) (.leaf 4452945367)) (.branch 6 (.leaf 4310501960) (.leaf 4174081173)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4043357336) (.leaf 3918026341)) (.branch 10 (.leaf 3797803906) (.leaf 3682424018))) (.branch 13 (.branch 12 (.leaf 3571637524) (.leaf 3465210846)) (.branch 14 (.leaf 3362924824) (.leaf 3264573654))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3169963923) (.branch 17 (.leaf 3078913728) (.leaf 2991251867))) (.branch 20 (.branch 19 (.leaf 2906817096) (.leaf 2825457454)) (.branch 21 (.leaf 2747029634) (.leaf 2671398406)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2598436088) (.leaf 2528022052)) (.branch 25 (.leaf 2460042275) (.leaf 2394388914))) (.branch 28 (.branch 27 (.leaf 2330959921) (.leaf 2269658680)) (.branch 29 (.leaf 2210393671) (.leaf 2153078161)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2097629915) (.branch 32 (.leaf 2043970921) (.leaf 1992027147))) (.branch 35 (.branch 34 (.leaf 1941728297) (.leaf 1893007602)) (.branch 36 (.leaf 1845801609) (.leaf 1800049995)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1755695383) (.leaf 1712683182)) (.branch 40 (.leaf 1670961423) (.leaf 1630480622))) (.branch 43 (.branch 42 (.leaf 1591193632) (.leaf 1553055525)) (.branch 44 (.leaf 1516023461) (.leaf 1480056584))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1445115909) (.branch 47 (.leaf 1411164223) (.leaf 1378165995))) (.branch 50 (.branch 49 (.leaf 1346087281) (.leaf 1314895648)) (.branch 51 (.leaf 1284560087) (.leaf 1255050949)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1226339866) (.leaf 1198399693)) (.branch 55 (.leaf 1171204440) (.leaf 1144729219))) (.branch 58 (.branch 57 (.leaf 1118950186) (.leaf 1093844488)) (.branch 59 (.leaf 1069390217) (.leaf 1045566362))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1022352766) (.branch 62 (.leaf 999730084) (.leaf 977679742))) (.branch 65 (.branch 64 (.leaf 956183904) (.leaf 935225435)) (.branch 66 (.leaf 914787866) (.leaf 894855368)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 875412715) (.leaf 856445261)) (.branch 70 (.leaf 837938914) (.leaf 819880106))) (.branch 73 (.branch 72 (.leaf 802255773) (.leaf 785053333)) (.branch 74 (.leaf 768260659) (.leaf 751866065))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 735858283) (.branch 77 (.leaf 720226445) (.leaf 704960068))) (.branch 80 (.branch 79 (.leaf 690049033) (.leaf 675483572)) (.branch 81 (.leaf 661254254) (.leaf 647351969)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 633767913) (.leaf 620493580)) (.branch 85 (.leaf 607520745) (.leaf 594841453))) (.branch 88 (.branch 87 (.leaf 582448013) (.leaf 570332978)) (.branch 89 (.leaf 558489145) (.leaf 546909538)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 535587404) (.branch 92 (.leaf 524516199) (.leaf 513689585))) (.branch 95 (.branch 94 (.leaf 503101418) (.leaf 492745745)) (.branch 96 (.leaf 482616792) (.leaf 472708958)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 463016811) (.leaf 453535082)) (.branch 100 (.leaf 444258654) (.leaf 435182562))) (.branch 103 (.branch 102 (.leaf 426301985) (.leaf 417612238)) (.branch 104 (.leaf 409108774) (.leaf 400787174))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392643141) (.leaf 384672502)) (.branch 108 (.leaf 376871197) (.leaf 369235280))) (.branch 111 (.branch 110 (.leaf 361760912) (.leaf 354444360)) (.branch 112 (.leaf 347281989) (.leaf 340270265)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333405747) (.leaf 326685084)) (.branch 116 (.leaf 320105015) (.leaf 313662363))) (.branch 119 (.branch 118 (.leaf 307354037) (.leaf 301177020)) (.branch 120 (.leaf 295128379) (.leaf 289205251)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 602).prefactor = (4702344227453507/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 602).cutoff/(generalMeanRows 602).c)).2 =
    (9737753075837/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 602).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 602).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 602).q*(generalMeanRows 602).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 602).q*(generalMeanRows 602).cutoff/2-2 = (5402/2563:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable208.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 602).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 602

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 602).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 602).criticalRate j.val*(generalMeanRows 602).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 602).c*(generalMeanRows 602).criticalPoint j.val)).2-
      (generalMeanRows 602).J/2-(generalMeanRows 602).error (generalMeanGrid j.val)+
      (generalMeanRows 602).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 602).c)).2-
      (generalMeanRows 602).J/2-(generalMeanRows 602).error 4 := by
  have he : (generalMeanRows 602).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 602) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 602)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0602

/-! Kernel-checked entropy margins for general spectral rectangle 603. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0603
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5015972121) (.branch 2 (.leaf 4845798846) (.leaf 4683224576))) (.branch 5 (.branch 4 (.leaf 4527815742) (.leaf 4379169420)) (.branch 6 (.leaf 4236910658) (.leaf 4100690088)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3970181790) (.leaf 3845081379)) (.branch 10 (.leaf 3725104271) (.leaf 3609984136))) (.branch 13 (.branch 12 (.leaf 3499471478) (.leaf 3393332370)) (.branch 14 (.leaf 3291347283) (.leaf 3193310037))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3099026834) (.branch 17 (.leaf 3008315376) (.leaf 2921004062))) (.branch 20 (.branch 19 (.leaf 2836931248) (.leaf 2755944566)) (.branch 21 (.leaf 2677900302) (.leaf 2602662819)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2530104027) (.leaf 2460102895)) (.branch 25 (.leaf 2392544995) (.leaf 2327322085))) (.branch 28 (.branch 27 (.leaf 2264331720) (.leaf 2203476893)) (.branch 29 (.leaf 2144665697) (.leaf 2087811017)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2032830241) (.branch 32 (.leaf 1979644989) (.leaf 1928180863))) (.branch 35 (.branch 34 (.leaf 1878367213) (.leaf 1830136919)) (.branch 36 (.leaf 1783426186) (.leaf 1738174355)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1694323722) (.leaf 1651819375)) (.branch 40 (.leaf 1610609035) (.leaf 1570642910))) (.branch 43 (.branch 42 (.leaf 1531873558) (.leaf 1494255761)) (.branch 44 (.leaf 1457746398) (.leaf 1422304340))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1387890335) (.branch 47 (.leaf 1354466914) (.leaf 1321998293))) (.branch 50 (.branch 49 (.leaf 1290450288) (.leaf 1259790228)) (.branch 51 (.leaf 1229986878) (.leaf 1201010368)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1172832117) (.leaf 1145424774)) (.branch 55 (.leaf 1118762149) (.leaf 1092819164))) (.branch 58 (.branch 57 (.leaf 1067571787) (.leaf 1042996988)) (.branch 59 (.leaf 1019072687) (.leaf 995777708))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 973091733) (.branch 62 (.leaf 950995263) (.leaf 929469580))) (.branch 65 (.branch 64 (.leaf 908496705) (.leaf 888059367)) (.branch 66 (.leaf 868140970) (.leaf 848725556)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 829797783) (.leaf 811342892)) (.branch 70 (.leaf 793346680) (.leaf 775795476))) (.branch 73 (.branch 72 (.leaf 758676119) (.leaf 741975929)) (.branch 74 (.leaf 725682693) (.leaf 709784639))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 694270418) (.branch 77 (.leaf 679129086) (.leaf 664350085))) (.branch 80 (.branch 79 (.leaf 649923230) (.leaf 635838689)) (.branch 81 (.leaf 622086968) (.leaf 608658900)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 595545628) (.leaf 582738596)) (.branch 85 (.leaf 570229530) (.leaf 558010434))) (.branch 88 (.branch 87 (.leaf 546073573) (.leaf 534411466)) (.branch 89 (.leaf 523016872) (.leaf 511882784)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 501002419) (.branch 92 (.leaf 490369208) (.leaf 479976787))) (.branch 95 (.branch 94 (.leaf 469818992) (.leaf 459889849)) (.branch 96 (.leaf 450183566) (.leaf 440694530)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431417295) (.leaf 422346580)) (.branch 100 (.leaf 413477261) (.leaf 404804365))) (.branch 103 (.branch 102 (.leaf 396323065) (.leaf 388028675)) (.branch 104 (.leaf 379916645) (.leaf 371982556))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364222113) (.leaf 356631145)) (.branch 108 (.leaf 349205598) (.leaf 341941531))) (.branch 111 (.branch 110 (.leaf 334835112) (.leaf 327882616)) (.branch 112 (.leaf 321080419) (.leaf 314424997)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 307912921) (.leaf 301540853)) (.branch 116 (.leaf 295305547) (.leaf 289203840))) (.branch 119 (.branch 118 (.leaf 283232656) (.leaf 277388997)) (.branch 120 (.leaf 271669945) (.leaf 266072658)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 603).prefactor = (9407724013679/2000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 603).cutoff/(generalMeanRows 603).c)).2 =
    (190280848904929/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 603).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 603).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 603).q*(generalMeanRows 603).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 603).q*(generalMeanRows 603).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 603).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 603

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 603).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 603).criticalRate j.val*(generalMeanRows 603).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 603).c*(generalMeanRows 603).criticalPoint j.val)).2-
      (generalMeanRows 603).J/2-(generalMeanRows 603).error (generalMeanGrid j.val)+
      (generalMeanRows 603).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 603).c)).2-
      (generalMeanRows 603).J/2-(generalMeanRows 603).error 4 := by
  have he : (generalMeanRows 603).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 603) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 603)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0603

/-! Kernel-checked entropy margins for general spectral rectangle 604. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0604
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5024627797) (.branch 2 (.leaf 4854160867) (.leaf 4691306055))) (.branch 5 (.branch 4 (.leaf 4535629044) (.leaf 4386726215)) (.branch 6 (.leaf 4244221968) (.leaf 4107766332)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3977032827) (.leaf 3851716539)) (.branch 10 (.leaf 3731532396) (.leaf 3616213607))) (.branch 13 (.branch 12 (.leaf 3505510246) (.leaf 3399187982)) (.branch 14 (.leaf 3297026907) (.leaf 3198820486))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3104374585) (.branch 17 (.leaf 3013506593) (.leaf 2926044613))) (.branch 20 (.branch 19 (.leaf 2841826721) (.leaf 2760700287)) (.branch 21 (.leaf 2682521348) (.leaf 2607154033)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2534470032) (.leaf 2464348105)) (.branch 25 (.leaf 2396673625) (.leaf 2331338165))) (.branch 28 (.branch 27 (.leaf 2268239103) (.leaf 2207279263)) (.branch 29 (.leaf 2148366581) (.leaf 2091413791)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2036338139) (.branch 32 (.leaf 1983061109) (.leaf 1931508176))) (.branch 35 (.branch 34 (.leaf 1881608566) (.leaf 1833295045)) (.branch 36 (.leaf 1786503707) (.leaf 1741173789)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1697247486) (.leaf 1654669793)) (.branch 40 (.leaf 1613388339) (.leaf 1573353247))) (.branch 43 (.branch 42 (.leaf 1534516994) (.leaf 1496834282)) (.branch 44 (.leaf 1460261919) (.leaf 1424758701))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1390285310) (.branch 47 (.leaf 1356804213) (.leaf 1324279563))) (.branch 50 (.branch 49 (.leaf 1292677118) (.leaf 1261964150)) (.branch 51 (.leaf 1232109372) (.leaf 1203082859)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1174855983) (.leaf 1147401345)) (.branch 55 (.leaf 1120692711) (.leaf 1094704957))) (.branch 58 (.branch 57 (.leaf 1069414013) (.leaf 1044796807)) (.branch 59 (.leaf 1020831222) (.leaf 997496044))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 974770922) (.branch 62 (.leaf 952636322) (.leaf 931073494))) (.branch 65 (.branch 64 (.leaf 910064428) (.leaf 889591823)) (.branch 66 (.leaf 869639053) (.leaf 850190136)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 831229701) (.leaf 812742964)) (.branch 70 (.leaf 794715697) (.leaf 777134206))) (.branch 73 (.branch 72 (.leaf 759985307) (.leaf 743256300)) (.branch 74 (.leaf 726934948) (.leaf 711009460))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 695468467) (.branch 77 (.leaf 680301006) (.leaf 665496503))) (.branch 80 (.branch 79 (.leaf 651044753) (.leaf 636935906)) (.branch 81 (.leaf 623160455) (.leaf 609709215)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 596573315) (.leaf 583744183)) (.branch 85 (.leaf 571213531) (.leaf 558973350))) (.branch 88 (.branch 87 (.leaf 547015890) (.leaf 535333658)) (.branch 89 (.leaf 523919402) (.leaf 512766101)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 501866960) (.branch 92 (.leaf 491215400) (.leaf 480805046))) (.branch 95 (.branch 94 (.leaf 470629722) (.leaf 460683445)) (.branch 96 (.leaf 450960413) (.leaf 441455003)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432161759) (.leaf 423075391)) (.branch 100 (.leaf 414190767) (.leaf 405502904))) (.branch 103 (.branch 102 (.leaf 397006969) (.leaf 388698266)) (.branch 104 (.leaf 380572238) (.leaf 372624457))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364850623) (.leaf 357246556)) (.branch 108 (.leaf 349808195) (.leaf 342531593))) (.branch 111 (.branch 110 (.leaf 335412911) (.leaf 328448417)) (.branch 112 (.leaf 321634483) (.leaf 314967576)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308444262) (.leaf 302061199)) (.branch 116 (.leaf 295815133) (.leaf 289702897))) (.branch 119 (.branch 118 (.leaf 283721408) (.leaf 277867666)) (.branch 120 (.leaf 272138745) (.leaf 266531799)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 604).prefactor = (942395819706823/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 604).cutoff/(generalMeanRows 604).c)).2 =
    (190280848904929/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 604).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 604).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 604).q*(generalMeanRows 604).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 604).q*(generalMeanRows 604).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 604).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 604

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 604).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 604).criticalRate j.val*(generalMeanRows 604).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 604).c*(generalMeanRows 604).criticalPoint j.val)).2-
      (generalMeanRows 604).J/2-(generalMeanRows 604).error (generalMeanGrid j.val)+
      (generalMeanRows 604).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 604).c)).2-
      (generalMeanRows 604).J/2-(generalMeanRows 604).error 4 := by
  have he : (generalMeanRows 604).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 604) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 604)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0604

/-! Kernel-checked entropy margins for general spectral rectangle 605. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0605
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4958992684) (.branch 2 (.leaf 4788410984) (.leaf 4625476207))) (.branch 5 (.branch 4 (.leaf 4469752327) (.leaf 4320834104)) (.branch 6 (.leaf 4178344408) (.leaf 4041931811)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3911268451) (.leaf 3786048099)) (.branch 10 (.leaf 3665984430) (.leaf 3550809459))) (.branch 13 (.branch 12 (.leaf 3440272123) (.leaf 3334137000)) (.branch 14 (.leaf 3232183145) (.leaf 3134203026))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3040001559) (.branch 17 (.leaf 2949395220) (.leaf 2862211239))) (.branch 20 (.branch 19 (.leaf 2778286855) (.leaf 2697468632)) (.branch 21 (.leaf 2619611838) (.leaf 2544579861)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2472243681) (.leaf 2402481372)) (.branch 25 (.leaf 2335177653) (.leaf 2270223465))) (.branch 28 (.branch 27 (.leaf 2207515579) (.leaf 2146956236)) (.branch 29 (.leaf 2088452811) (.leaf 2031917498)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1977267023) (.branch 32 (.leaf 1924422371) (.leaf 1873308536))) (.branch 35 (.branch 34 (.leaf 1823854283) (.leaf 1775991930)) (.branch 36 (.leaf 1729657144) (.leaf 1684788749)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1641328546) (.leaf 1599221145)) (.branch 40 (.leaf 1558413810) (.leaf 1518856311))) (.branch 43 (.branch 42 (.leaf 1480500783) (.leaf 1443301604)) (.branch 44 (.leaf 1407215265) (.leaf 1372200263))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1338216987) (.branch 47 (.leaf 1305227626) (.leaf 1273196065))) (.branch 50 (.branch 49 (.leaf 1242087803) (.leaf 1211869866)) (.branch 51 (.leaf 1182510728) (.leaf 1153980237)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1126249546) (.leaf 1099291045)) (.branch 55 (.leaf 1073078300) (.leaf 1047585994))) (.branch 58 (.branch 57 (.leaf 1022789870) (.leaf 998666681)) (.branch 59 (.leaf 975194138) (.leaf 952350867))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 930116360) (.branch 62 (.leaf 908470936) (.leaf 887395702))) (.branch 65 (.branch 64 (.leaf 866872512) (.leaf 846883938)) (.branch 66 (.leaf 827413229) (.leaf 808444284)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 789961623) (.leaf 771950353)) (.branch 70 (.leaf 754396147) (.leaf 737285213))) (.branch 73 (.branch 72 (.leaf 720604276) (.leaf 704340549)) (.branch 74 (.leaf 688481714) (.leaf 673015901))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 657931669) (.branch 77 (.leaf 643217986) (.leaf 628864211))) (.branch 80 (.branch 79 (.leaf 614860078) (.leaf 601195681)) (.branch 81 (.leaf 587861457) (.leaf 574848171)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 562146905) (.leaf 549749042)) (.branch 85 (.leaf 537646256) (.leaf 525830497))) (.branch 88 (.branch 87 (.leaf 514293982) (.leaf 503029184)) (.branch 89 (.leaf 492028823) (.leaf 481285851)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 470793449) (.branch 92 (.leaf 460545016) (.leaf 450534156))) (.branch 95 (.branch 94 (.leaf 440754678) (.leaf 431200582)) (.branch 96 (.leaf 421866055) (.leaf 412745460)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 403833335) (.leaf 395124382)) (.branch 100 (.leaf 386613463) (.leaf 378295592))) (.branch 103 (.branch 102 (.leaf 370165932) (.leaf 362219789)) (.branch 104 (.leaf 354452606) (.leaf 346859957))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 339437547) (.leaf 332181201)) (.branch 108 (.leaf 325086864) (.leaf 318150598))) (.branch 111 (.branch 110 (.leaf 311368572) (.leaf 304737065)) (.branch 112 (.leaf 298252459) (.leaf 291911234)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285709970) (.leaf 279645337)) (.branch 116 (.leaf 273714098) (.leaf 267913102))) (.branch 119 (.branch 118 (.leaf 262239283) (.leaf 256689656)) (.branch 120 (.leaf 251261316) (.leaf 245951436)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 605).prefactor = (189130213088423/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 605).cutoff/(generalMeanRows 605).c)).2 =
    (93274744152067/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 605).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 605).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 605).q*(generalMeanRows 605).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 605).q*(generalMeanRows 605).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 605).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 605

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 605).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 605).criticalRate j.val*(generalMeanRows 605).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 605).c*(generalMeanRows 605).criticalPoint j.val)).2-
      (generalMeanRows 605).J/2-(generalMeanRows 605).error (generalMeanGrid j.val)+
      (generalMeanRows 605).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 605).c)).2-
      (generalMeanRows 605).J/2-(generalMeanRows 605).error 4 := by
  have he : (generalMeanRows 605).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 605) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 605)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0605

/-! Kernel-checked entropy margins for general spectral rectangle 606. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0606
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4911547204) (.branch 2 (.leaf 4740293245) (.leaf 4576747164))) (.branch 5 (.branch 4 (.leaf 4420469679) (.leaf 4271052504)) (.branch 6 (.leaf 4128115638) (.leaf 3991304959)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3860290060) (.leaf 3734762318)) (.branch 10 (.leaf 3614433144) (.leaf 3499032412))) (.branch 13 (.branch 12 (.leaf 3388307034) (.leaf 3282019671)) (.branch 14 (.leaf 3179947558) (.leaf 3081881440))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2987624591) (.branch 17 (.leaf 2896991933) (.leaf 2809809214))) (.branch 20 (.branch 19 (.leaf 2725912265) (.leaf 2645146309)) (.branch 21 (.leaf 2567365335) (.leaf 2492431514)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2420214663) (.leaf 2350591750)) (.branch 25 (.leaf 2283446436) (.leaf 2218668651))) (.branch 28 (.branch 27 (.leaf 2156154202) (.leaf 2095804409)) (.branch 29 (.leaf 2037525764) (.leaf 1981229620)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1926831898) (.branch 32 (.leaf 1874252811) (.leaf 1823416616))) (.branch 35 (.branch 34 (.leaf 1774251371) (.leaf 1726688721)) (.branch 36 (.leaf 1680663686) (.leaf 1636114469)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1592982278) (.leaf 1551211157)) (.branch 40 (.leaf 1510747826) (.leaf 1471541532))) (.branch 43 (.branch 42 (.leaf 1433543914) (.leaf 1396708869)) (.branch 44 (.leaf 1360992431) (.leaf 1326352659))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1292749523) (.branch 47 (.leaf 1260144806) (.leaf 1228502011))) (.branch 50 (.branch 49 (.leaf 1197786266) (.leaf 1167964244)) (.branch 51 (.leaf 1139004080) (.leaf 1110875298)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1083548741) (.leaf 1056996501)) (.branch 55 (.leaf 1031191860) (.leaf 1006109228))) (.branch 58 (.branch 57 (.leaf 981724090) (.leaf 958012948)) (.branch 59 (.leaf 934953277) (.leaf 912523473))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 890702812) (.branch 62 (.leaf 869471405) (.leaf 848810159))) (.branch 65 (.branch 64 (.leaf 828700741) (.leaf 809125540)) (.branch 66 (.leaf 790067634) (.leaf 771510757)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 753439272) (.leaf 735838136)) (.branch 70 (.leaf 718692881) (.leaf 701989579))) (.branch 73 (.branch 72 (.leaf 685714826) (.leaf 669855712)) (.branch 74 (.leaf 654399804) (.leaf 639335122))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 624650118) (.branch 77 (.leaf 610333662) (.leaf 596375020))) (.branch 80 (.branch 79 (.leaf 582763836) (.leaf 569490121)) (.branch 81 (.leaf 556544231) (.leaf 543916858)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 531599013) (.leaf 519582013)) (.branch 85 (.leaf 507857469) (.leaf 496417273))) (.branch 88 (.branch 87 (.leaf 485253589) (.leaf 474358838)) (.branch 89 (.leaf 463725691) (.leaf 453347058)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 443216078) (.branch 92 (.leaf 433326112) (.leaf 423670730))) (.branch 95 (.branch 94 (.leaf 414243709) (.leaf 405039019)) (.branch 96 (.leaf 396050819) (.leaf 387273451)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 378701429) (.leaf 370329436)) (.branch 100 (.leaf 362152316) (.leaf 354165070))) (.branch 103 (.branch 102 (.leaf 346362847) (.leaf 338740942)) (.branch 104 (.leaf 331294788) (.leaf 324019954))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316912136) (.leaf 309967159)) (.branch 108 (.leaf 303180963) (.leaf 296549610))) (.branch 111 (.branch 110 (.leaf 290069271) (.leaf 283736225)) (.branch 112 (.leaf 277546859) (.leaf 271497657)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265585205) (.leaf 259806182)) (.branch 116 (.leaf 254157357) (.leaf 248635588))) (.branch 119 (.branch 118 (.leaf 243237821) (.leaf 237961082)) (.branch 120 (.leaf 232802479) (.leaf 227759195)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 606).prefactor = (2380488321979003/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 606).cutoff/(generalMeanRows 606).c)).2 =
    (182845767665203/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 606).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 606).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 606).q*(generalMeanRows 606).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 606).q*(generalMeanRows 606).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 606).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 606

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 606).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 606).criticalRate j.val*(generalMeanRows 606).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 606).c*(generalMeanRows 606).criticalPoint j.val)).2-
      (generalMeanRows 606).J/2-(generalMeanRows 606).error (generalMeanGrid j.val)+
      (generalMeanRows 606).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 606).c)).2-
      (generalMeanRows 606).J/2-(generalMeanRows 606).error 4 := by
  have he : (generalMeanRows 606).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 606) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 606)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0606

/-! Kernel-checked entropy margins for general spectral rectangle 607. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0607
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4897875237) (.branch 2 (.leaf 4727157219) (.leaf 4564108854))) (.branch 5 (.branch 4 (.leaf 4408294011) (.leaf 4259307288)) (.branch 6 (.leaf 4116771333) (.leaf 3980334452)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3849668465) (.leaf 3724466794)) (.branch 10 (.leaf 3604442724) (.leaf 3489327853))) (.branch 13 (.branch 12 (.leaf 3378870673) (.leaf 3272835295)) (.branch 14 (.leaf 3171000286) (.leaf 3073157613))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2979111675) (.branch 17 (.leaf 2888678419) (.leaf 2801684541))) (.branch 20 (.branch 19 (.leaf 2717966736) (.leaf 2637371023)) (.branch 21 (.leaf 2559752119) (.leaf 2484972864)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2412903687) (.leaf 2343422115)) (.branch 25 (.leaf 2276412323) (.leaf 2211764710))) (.branch 28 (.branch 27 (.leaf 2149375515) (.leaf 2089146448)) (.branch 29 (.leaf 2030984362) (.leaf 1974800938)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1920512395) (.branch 32 (.leaf 1868039220) (.leaf 1817305918))) (.branch 35 (.branch 34 (.leaf 1768240777) (.leaf 1720775644)) (.branch 36 (.leaf 1674845729) (.leaf 1630389406)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1587348038) (.leaf 1545665809)) (.branch 40 (.leaf 1505289565) (.leaf 1466168672))) (.branch 43 (.branch 42 (.leaf 1428254870) (.leaf 1391502153)) (.branch 44 (.leaf 1355866639) (.leaf 1321306462))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1287781663) (.branch 47 (.leaf 1255254088) (.leaf 1223687294))) (.branch 50 (.branch 49 (.leaf 1193046460) (.leaf 1163298302)) (.branch 51 (.leaf 1134410998) (.leaf 1106354106)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1079098500) (.leaf 1052616303)) (.branch 55 (.leaf 1026880820) (.leaf 1001866485))) (.branch 58 (.branch 57 (.leaf 977548801) (.leaf 953904289)) (.branch 59 (.leaf 930910439) (.leaf 908545662))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 886789244) (.branch 62 (.leaf 865621307) (.leaf 845022770))) (.branch 65 (.branch 64 (.leaf 824975306) (.leaf 805461311)) (.branch 66 (.leaf 786463871) (.leaf 767966725)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 749954241) (.leaf 732411382)) (.branch 70 (.leaf 715323681) (.leaf 698677218))) (.branch 73 (.branch 72 (.leaf 682458591) (.leaf 666654892)) (.branch 74 (.leaf 651253693) (.leaf 636243015))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 621611314) (.branch 77 (.leaf 607347464) (.leaf 593440731))) (.branch 80 (.branch 79 (.leaf 579880765) (.leaf 566657578)) (.branch 81 (.leaf 553761530) (.leaf 541183315)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 528913948) (.leaf 516944748)) (.branch 85 (.leaf 505267330) (.leaf 493873591))) (.branch 88 (.branch 87 (.leaf 482755695) (.leaf 471906070)) (.branch 89 (.leaf 461317390) (.leaf 450982569)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440894750) (.branch 92 (.leaf 431047298) (.leaf 421433788))) (.branch 95 (.branch 94 (.leaf 412048001) (.leaf 402883913)) (.branch 96 (.leaf 393935686) (.leaf 385197669)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 376664379) (.leaf 368330506)) (.branch 100 (.leaf 360190899) (.leaf 352240564))) (.branch 103 (.branch 102 (.leaf 344474655) (.leaf 336888475)) (.branch 104 (.leaf 329477461) (.leaf 322237188))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315163359) (.leaf 308251803)) (.branch 108 (.leaf 301498469) (.leaf 294899423))) (.branch 111 (.branch 110 (.leaf 288450843) (.leaf 282149015)) (.branch 112 (.leaf 275990330) (.leaf 269971282)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264088460) (.leaf 258338551)) (.branch 116 (.leaf 252718331) (.leaf 247224665))) (.branch 119 (.branch 118 (.leaf 241854503) (.leaf 236604880)) (.branch 120 (.leaf 231472908) (.leaf 226455780)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 607).prefactor = (236575744042127/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 607).cutoff/(generalMeanRows 607).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 607).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 607).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 607).q*(generalMeanRows 607).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 607).q*(generalMeanRows 607).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 607).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 607

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 607).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 607).criticalRate j.val*(generalMeanRows 607).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 607).c*(generalMeanRows 607).criticalPoint j.val)).2-
      (generalMeanRows 607).J/2-(generalMeanRows 607).error (generalMeanGrid j.val)+
      (generalMeanRows 607).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 607).c)).2-
      (generalMeanRows 607).J/2-(generalMeanRows 607).error 4 := by
  have he : (generalMeanRows 607).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 607) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 607)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0607

/-! Kernel-checked entropy margins for general spectral rectangle 608. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0608
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4969084002) (.branch 2 (.leaf 4798180515) (.leaf 4634931356))) (.branch 5 (.branch 4 (.leaf 4478900563) (.leaf 4329682940)) (.branch 6 (.leaf 4186901371) (.leaf 4050204430)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3919264230) (.leaf 3793774505)) (.branch 10 (.leaf 3673448877) (.leaf 3558019292))) (.branch 13 (.branch 12 (.leaf 3447234606) (.leaf 3340859309)) (.branch 14 (.leaf 3238672355) (.leaf 3140466103))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3046045353) (.branch 17 (.leaf 2955226460) (.leaf 2867836526))) (.branch 20 (.branch 19 (.leaf 2783712659) (.leaf 2702701288)) (.branch 21 (.leaf 2624657542) (.leaf 2549444669)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2476933505) (.leaf 2407001984)) (.branch 25 (.leaf 2339534680) (.leaf 2274422388))) (.branch 28 (.branch 27 (.leaf 2211561737) (.leaf 2150854824)) (.branch 29 (.leaf 2092208881) (.leaf 2035535962)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1980752651) (.branch 32 (.leaf 1927779797) (.leaf 1876542255))) (.branch 35 (.branch 34 (.leaf 1826968658) (.leaf 1778991190)) (.branch 36 (.leaf 1732545388) (.leaf 1687569950)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1644006550) (.leaf 1601799676)) (.branch 40 (.leaf 1560896473) (.leaf 1521246592))) (.branch 43 (.branch 42 (.leaf 1482802057) (.leaf 1445517130)) (.branch 44 (.leaf 1409348195) (.leaf 1374253642))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1340193758) (.branch 47 (.leaf 1307130630) (.leaf 1275028046))) (.branch 50 (.branch 49 (.leaf 1243851410) (.leaf 1213567654)) (.branch 51 (.leaf 1184145164) (.leaf 1155553699)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1127764329) (.leaf 1100749361)) (.branch 55 (.leaf 1074482283) (.leaf 1048937698))) (.branch 58 (.branch 57 (.leaf 1024091277) (.leaf 999919700)) (.branch 59 (.leaf 976400609) (.leaf 953512562))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 931234984) (.branch 62 (.leaf 909548133) (.leaf 888433053))) (.branch 65 (.branch 64 (.leaf 867871541) (.leaf 847846110)) (.branch 66 (.leaf 828339955) (.leaf 809336923)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 790821480) (.leaf 772778686)) (.branch 70 (.leaf 755194164) (.leaf 738054079))) (.branch 73 (.branch 72 (.leaf 721345109) (.leaf 705054424)) (.branch 74 (.leaf 689169667) (.leaf 673678927))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 658570724) (.branch 77 (.leaf 643833990) (.leaf 629458047))) (.branch 80 (.branch 79 (.leaf 615432598) (.leaf 601747701)) (.branch 81 (.leaf 588393762) (.leaf 575361516)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 562642016) (.leaf 550226616)) (.branch 85 (.leaf 538106962) (.leaf 526274979))) (.branch 88 (.branch 87 (.leaf 514722859) (.leaf 503443050)) (.branch 89 (.leaf 492428249) (.leaf 481671386)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 471165620) (.branch 92 (.leaf 460904328) (.leaf 450881097))) (.branch 95 (.branch 94 (.leaf 441089715) (.leaf 431524164)) (.branch 96 (.leaf 422178613) (.leaf 413047409)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 404125073) (.leaf 395406292)) (.branch 100 (.leaf 386885911) (.leaf 378558931))) (.branch 103 (.branch 102 (.leaf 370420502) (.leaf 362465916)) (.branch 104 (.leaf 354690602) (.leaf 347090123))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 339660172) (.leaf 332396562)) (.branch 108 (.leaf 325295228) (.leaf 318352221))) (.branch 111 (.branch 110 (.leaf 311563700) (.leaf 304925934)) (.branch 112 (.leaf 298435297) (.leaf 292088259)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285881392) (.leaf 279811358)) (.branch 116 (.leaf 273874911) (.leaf 268068894))) (.branch 119 (.branch 118 (.leaf 262390232) (.leaf 256835935)) (.branch 120 (.leaf 251403090) (.leaf 246088863)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 608).prefactor = (189195348542361/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 608).cutoff/(generalMeanRows 608).c)).2 =
    (371671424617083/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 608).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 608).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 608).q*(generalMeanRows 608).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 608).q*(generalMeanRows 608).cutoff/2-2 = (16162/7711:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable209.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 608).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 608

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 608).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 608).criticalRate j.val*(generalMeanRows 608).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 608).c*(generalMeanRows 608).criticalPoint j.val)).2-
      (generalMeanRows 608).J/2-(generalMeanRows 608).error (generalMeanGrid j.val)+
      (generalMeanRows 608).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 608).c)).2-
      (generalMeanRows 608).J/2-(generalMeanRows 608).error 4 := by
  have he : (generalMeanRows 608).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 608) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 608)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0608

/-! Kernel-checked entropy margins for general spectral rectangle 609. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0609
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4977694154) (.branch 2 (.leaf 4806494535) (.leaf 4642962507))) (.branch 5 (.branch 4 (.leaf 4486661353) (.leaf 4337185173)) (.branch 6 (.leaf 4194156201) (.leaf 4057222399)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3926055313) (.leaf 3800348147)) (.branch 10 (.leaf 3679814025) (.leaf 3564184429))) (.branch 13 (.branch 12 (.leaf 3453207783) (.leaf 3346648164)) (.branch 14 (.leaf 3244284146) (.leaf 3145907728))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3051323371) (.branch 17 (.leaf 2960347112) (.leaf 2872805754))) (.branch 20 (.branch 19 (.leaf 2788536121) (.leaf 2707384378)) (.branch 21 (.leaf 2629205402) (.leaf 2553862205)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2481225398) (.leaf 2411172703)) (.branch 25 (.leaf 2343588495) (.leaf 2278363381))) (.branch 28 (.branch 27 (.leaf 2215393808) (.leaf 2154581706)) (.branch 29 (.leaf 2095834144) (.leaf 2039063025)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1984184789) (.branch 32 (.leaf 1931120147) (.leaf 1879793823))) (.branch 35 (.branch 34 (.leaf 1830134327) (.leaf 1782073727)) (.branch 36 (.leaf 1735547447) (.leaf 1690494077)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1646855193) (.leaf 1604575186)) (.branch 40 (.leaf 1563601108) (.leaf 1523882524))) (.branch 43 (.branch 42 (.leaf 1485371374) (.leaf 1448021841)) (.branch 44 (.leaf 1411790235) (.leaf 1376634872))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1342515972) (.branch 47 (.leaf 1309395553) (.leaf 1277237344))) (.branch 50 (.branch 49 (.leaf 1246006686) (.leaf 1215670457)) (.branch 51 (.leaf 1186196984) (.leaf 1157555978)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1129718456) (.leaf 1102656679)) (.branch 55 (.leaf 1076344086) (.leaf 1050755239))) (.branch 58 (.branch 57 (.leaf 1025865765) (.leaf 1001652305)) (.branch 59 (.leaf 978092462) (.leaf 955164755))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 932848576) (.branch 62 (.leaf 911124147) (.leaf 889972480))) (.branch 65 (.branch 64 (.leaf 869375340) (.leaf 849315210)) (.branch 66 (.leaf 829775256) (.leaf 810739297)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 792191771) (.leaf 774117714)) (.branch 70 (.leaf 756502723) (.leaf 739332938))) (.branch 73 (.branch 72 (.leaf 722595015) (.leaf 706276103)) (.branch 74 (.leaf 690363822) (.leaf 674846240))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 659711859) (.branch 77 (.leaf 644949589) (.leaf 630548737))) (.branch 80 (.branch 79 (.leaf 616498985) (.leaf 602790376)) (.branch 81 (.leaf 589413298) (.leaf 576358471)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 563616931) (.leaf 551180018)) (.branch 85 (.leaf 539039364) (.leaf 527186879))) (.branch 88 (.branch 87 (.leaf 515614742) (.leaf 504315388)) (.branch 89 (.leaf 493281501) (.leaf 482505999)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 471982029) (.branch 92 (.leaf 461702957) (.leaf 451662359))) (.branch 95 (.branch 94 (.leaf 441854011) (.leaf 432271885)) (.branch 96 (.leaf 422910141) (.leaf 413763115)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 404825319) (.leaf 396091430)) (.branch 100 (.leaf 387556285) (.leaf 379214877))) (.branch 103 (.branch 102 (.leaf 371062346) (.leaf 363093976)) (.branch 104 (.leaf 355305190) (.leaf 347691542))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 340248716) (.leaf 332972520)) (.branch 108 (.leaf 325858882) (.leaf 318903844))) (.branch 111 (.branch 110 (.leaf 312103560) (.leaf 305454293)) (.branch 112 (.leaf 298952409) (.leaf 292594374)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 286376751) (.leaf 280296199)) (.branch 116 (.leaf 274349466) (.leaf 268533389))) (.branch 119 (.branch 118 (.leaf 262844887) (.leaf 257280966)) (.branch 120 (.leaf 251838707) (.leaf 246515272)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 609).prefactor = (947615878560053/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 609).cutoff/(generalMeanRows 609).c)).2 =
    (371671424617083/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 609).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 609).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 609).q*(generalMeanRows 609).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 609).q*(generalMeanRows 609).cutoff/2-2 = (16162/7711:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable209.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 609).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 609

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 609).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 609).criticalRate j.val*(generalMeanRows 609).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 609).c*(generalMeanRows 609).criticalPoint j.val)).2-
      (generalMeanRows 609).J/2-(generalMeanRows 609).error (generalMeanGrid j.val)+
      (generalMeanRows 609).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 609).c)).2-
      (generalMeanRows 609).J/2-(generalMeanRows 609).error 4 := by
  have he : (generalMeanRows 609).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 609) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 609)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0609

/-! Kernel-checked entropy margins for general spectral rectangle 610. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0610
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4906397131) (.branch 2 (.leaf 4735382079) (.leaf 4572050023))) (.branch 5 (.branch 4 (.leaf 4415964075) (.leaf 4266718128)) (.branch 6 (.leaf 4123934172) (.leaf 3987259902)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3856366567) (.leaf 3730947055)) (.branch 10 (.leaf 3610714154) (.leaf 3495398992))) (.branch 13 (.branch 12 (.leaf 3384749626) (.leaf 3278529755)) (.branch 14 (.leaf 3176517562) (.leaf 3078504651))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2984295081) (.branch 17 (.leaf 2893704479) (.leaf 2806559239))) (.branch 20 (.branch 19 (.leaf 2722695771) (.leaf 2641959828)) (.branch 21 (.leaf 2564205875) (.leaf 2489296510)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2417101938) (.leaf 2347499474)) (.branch 25 (.leaf 2280373090) (.leaf 2215612997))) (.branch 28 (.branch 27 (.leaf 2153115249) (.leaf 2092781389)) (.branch 29 (.leaf 2034518106) (.leaf 1978236927)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1923853926) (.branch 32 (.leaf 1871289452) (.leaf 1820467879))) (.branch 35 (.branch 34 (.leaf 1771317368) (.leaf 1723769650)) (.branch 36 (.leaf 1677759821) (.leaf 1633226147)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1590109891) (.leaf 1548355138)) (.branch 40 (.leaf 1507908644) (.leaf 1468719683))) (.branch 43 (.branch 42 (.leaf 1430739915) (.leaf 1393923250)) (.branch 44 (.leaf 1358225734) (.leaf 1323605425))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1290022296) (.branch 47 (.leaf 1257438126) (.leaf 1225816408))) (.branch 50 (.branch 49 (.leaf 1195122261) (.leaf 1165322345)) (.branch 51 (.leaf 1136384778) (.leaf 1108279070)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1080976042) (.leaf 1054447767)) (.branch 55 (.leaf 1028667507) (.leaf 1003609649))) (.branch 58 (.branch 57 (.leaf 979249654) (.leaf 955564003)) (.branch 59 (.leaf 932530146) (.leaf 910126455))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 888332183) (.branch 62 (.leaf 867127416) (.leaf 846493039))) (.branch 65 (.branch 64 (.leaf 826410694) (.leaf 806862746)) (.branch 66 (.leaf 787832252) (.leaf 769302923)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 751259099) (.leaf 733685716)) (.branch 70 (.leaf 716568285) (.leaf 699892859))) (.branch 73 (.branch 72 (.leaf 683646012) (.leaf 667814816)) (.branch 74 (.leaf 652386820) (.leaf 637350024))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 622692866) (.branch 77 (.leaf 608404198) (.leaf 594473269))) (.branch 80 (.branch 79 (.leaf 580889710) (.leaf 567643515)) (.branch 81 (.leaf 554725029) (.leaf 542124929)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 529834214) (.leaf 517844189)) (.branch 85 (.leaf 506146453) (.leaf 494732889))) (.branch 88 (.branch 87 (.leaf 483595650) (.leaf 472727148)) (.branch 89 (.leaf 462120044) (.leaf 451767241)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 441661870) (.branch 92 (.leaf 431797284) (.leaf 422167048))) (.branch 95 (.branch 94 (.leaf 412764930) (.leaf 403584897)) (.branch 96 (.leaf 394621102) (.leaf 385867880)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377319744) (.leaf 368971370)) (.branch 100 (.leaf 360817601) (.leaf 352853433))) (.branch 103 (.branch 102 (.leaf 345074013) (.leaf 337474632)) (.branch 104 (.leaf 330050724) (.leaf 322797854))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315711717) (.leaf 308788136)) (.branch 108 (.leaf 302023052) (.leaf 295412524))) (.branch 111 (.branch 110 (.leaf 288952723) (.leaf 282639930)) (.branch 112 (.leaf 276470530) (.leaf 270441009)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264547952) (.leaf 258788039)) (.branch 116 (.leaf 253158040) (.leaf 247654815))) (.branch 119 (.branch 118 (.leaf 242275310) (.leaf 237016553)) (.branch 120 (.leaf 231875652) (.leaf 226849795)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 610).prefactor = (4739747322263501/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 610).cutoff/(generalMeanRows 610).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 610).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 610).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 610).q*(generalMeanRows 610).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 610).q*(generalMeanRows 610).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 610).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 610

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 610).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 610).criticalRate j.val*(generalMeanRows 610).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 610).c*(generalMeanRows 610).criticalPoint j.val)).2-
      (generalMeanRows 610).J/2-(generalMeanRows 610).error (generalMeanGrid j.val)+
      (generalMeanRows 610).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 610).c)).2-
      (generalMeanRows 610).J/2-(generalMeanRows 610).error 4 := by
  have he : (generalMeanRows 610).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 610) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 610)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0610

/-! Kernel-checked entropy margins for general spectral rectangle 611. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0611
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4914933853) (.branch 2 (.leaf 4743621249) (.leaf 4580005009))) (.branch 5 (.branch 4 (.leaf 4423647484) (.leaf 4274141862)) (.branch 6 (.leaf 4131109474) (.leaf 3994197401)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3863076324) (.leaf 3737438592)) (.branch 10 (.leaf 3616996496) (.leaf 3501480695))) (.branch 13 (.branch 12 (.leaf 3390638808) (.leaf 3284234123)) (.branch 14 (.leaf 3182044438) (.leaf 3083860993))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2989487505) (.branch 17 (.leaf 2898739284) (.leaf 2811442418))) (.branch 20 (.branch 19 (.leaf 2727433035) (.leaf 2646556618)) (.branch 21 (.leaf 2568667379) (.leaf 2493627678)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2421307494) (.leaf 2351583927)) (.branch 25 (.leaf 2284340749) (.leaf 2219467978))) (.branch 28 (.branch 27 (.leaf 2156861490) (.leaf 2096422654)) (.branch 29 (.leaf 2038057997) (.leaf 1981678894)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1927201271) (.branch 32 (.leaf 1874545340) (.leaf 1823635341))) (.branch 35 (.branch 34 (.leaf 1774399313) (.leaf 1726768866)) (.branch 36 (.leaf 1680678983) (.leaf 1636067825)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1592876550) (.leaf 1551049147)) (.branch 40 (.leaf 1510532279) (.leaf 1471275133))) (.branch 43 (.branch 42 (.leaf 1433229283) (.leaf 1396348561)) (.branch 44 (.leaf 1360588933) (.leaf 1325908388))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1292266827) (.branch 47 (.leaf 1259625963) (.leaf 1227949226))) (.branch 50 (.branch 49 (.leaf 1197201674) (.leaf 1167349908)) (.branch 51 (.leaf 1138361993) (.leaf 1110207383)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1082856850) (.leaf 1056282419)) (.branch 55 (.leaf 1030457303) (.leaf 1005355846))) (.branch 58 (.branch 57 (.leaf 980953467) (.leaf 957226605)) (.branch 59 (.leaf 934152671) (.leaf 911710000))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 889877807) (.branch 62 (.leaf 868636146) (.leaf 847965866))) (.branch 65 (.branch 64 (.leaf 827848579) (.leaf 808266620)) (.branch 66 (.leaf 789203015) (.leaf 770641446)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 752566227) (.leaf 734962268)) (.branch 70 (.leaf 717815054) (.leaf 701110614))) (.branch 73 (.branch 72 (.leaf 684835499) (.leaf 668976758)) (.branch 74 (.leaf 653521918) (.leaf 638458960))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 623776300) (.branch 77 (.leaf 609462770) (.leaf 595507603))) (.branch 80 (.branch 79 (.leaf 581900409) (.leaf 568631167)) (.branch 81 (.leaf 555690204) (.leaf 543068181)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 530756081) (.leaf 518745194)) (.branch 85 (.leaf 507027106) (.leaf 495593683))) (.branch 88 (.branch 87 (.leaf 484437066) (.leaf 473549653)) (.branch 89 (.leaf 462924094) (.leaf 452553279)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 442430325) (.branch 92 (.leaf 432548576) (.leaf 422901584))) (.branch 95 (.branch 94 (.leaf 413483107) (.leaf 404287101)) (.branch 96 (.leaf 395307709) (.leaf 386539258)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377976249) (.leaf 369613350)) (.branch 100 (.leaf 361445394) (.leaf 353467368))) (.branch 103 (.branch 102 (.leaf 345674413) (.leaf 338061810)) (.branch 104 (.leaf 330624985) (.leaf 323359495))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316261029) (.leaf 309325401)) (.branch 108 (.leaf 302548546) (.leaf 295926517))) (.branch 111 (.branch 110 (.leaf 289455477) (.leaf 283131700)) (.branch 112 (.leaf 276951566) (.leaf 270911554)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265008244) (.leaf 259238308)) (.branch 116 (.leaf 253598514) (.leaf 248085714))) (.branch 119 (.branch 118 (.leaf 242696849) (.leaf 237428942)) (.branch 120 (.leaf 232279096) (.leaf 227244494)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 611).prefactor = (4747994087446189/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 611).cutoff/(generalMeanRows 611).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 611).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 611).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 611).q*(generalMeanRows 611).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 611).q*(generalMeanRows 611).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 611).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 611

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 611).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 611).criticalRate j.val*(generalMeanRows 611).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 611).c*(generalMeanRows 611).criticalPoint j.val)).2-
      (generalMeanRows 611).J/2-(generalMeanRows 611).error (generalMeanGrid j.val)+
      (generalMeanRows 611).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 611).c)).2-
      (generalMeanRows 611).J/2-(generalMeanRows 611).error 4 := by
  have he : (generalMeanRows 611).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 611) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 611)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0611

/-! Kernel-checked entropy margins for general spectral rectangle 612. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0612
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5214004871) (.branch 2 (.leaf 5046909798) (.leaf 4887174316))) (.branch 5 (.branch 4 (.leaf 4734376198) (.leaf 4588123228)) (.branch 6 (.leaf 4448050578) (.leaf 4313818467)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4185110065) (.leaf 4061629615)) (.branch 10 (.leaf 3943100739) (.leaf 3829264912))) (.branch 13 (.branch 12 (.leaf 3719880078) (.leaf 3614719396)) (.branch 14 (.leaf 3513570105) (.leaf 3416232486))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3322518913) (.branch 17 (.leaf 3232252995) (.leaf 3145268780))) (.branch 20 (.branch 19 (.leaf 3061410032) (.leaf 2980529563)) (.branch 21 (.leaf 2902488623) (.leaf 2827156333)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2754409169) (.leaf 2684130475)) (.branch 25 (.leaf 2616210026) (.leaf 2550543613))) (.branch 28 (.branch 27 (.leaf 2487032661) (.leaf 2425583883)) (.branch 29 (.leaf 2366108942) (.leaf 2308524155)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2252750208) (.branch 32 (.leaf 2198711888) (.leaf 2146337842))) (.branch 35 (.branch 34 (.leaf 2095560347) (.leaf 2046315096)) (.branch 36 (.leaf 1998541000) (.leaf 1952179998)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1907176889) (.leaf 1863479161)) (.branch 40 (.leaf 1821036848) (.leaf 1779802379))) (.branch 43 (.branch 42 (.leaf 1739730450) (.leaf 1700777893)) (.branch 44 (.leaf 1662903565) (.leaf 1626068233))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1590234469) (.branch 47 (.leaf 1555366559) (.leaf 1521430404))) (.branch 50 (.branch 49 (.leaf 1488393439) (.leaf 1456224551)) (.branch 51 (.leaf 1424894000) (.leaf 1394373351)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1364635406) (.leaf 1335654137)) (.branch 55 (.leaf 1307404629) (.leaf 1279863023))) (.branch 58 (.branch 57 (.leaf 1253006464) (.leaf 1226813046)) (.branch 59 (.leaf 1201261769) (.leaf 1176332494))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1152005898) (.branch 62 (.leaf 1128263436) (.leaf 1105087301))) (.branch 65 (.branch 64 (.leaf 1082460393) (.leaf 1060366279)) (.branch 66 (.leaf 1038789166) (.leaf 1017713869)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 997125781) (.leaf 977010847)) (.branch 70 (.leaf 957355541) (.leaf 938146837))) (.branch 73 (.branch 72 (.leaf 919372190) (.leaf 901019509)) (.branch 74 (.leaf 883077144) (.leaf 865533859))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 848378819) (.branch 77 (.leaf 831601568) (.leaf 815192015))) (.branch 80 (.branch 79 (.leaf 799140416) (.leaf 783437363)) (.branch 81 (.leaf 768073763) (.leaf 753040832)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 738330075) (.leaf 723933279)) (.branch 85 (.leaf 709842499) (.leaf 696050046))) (.branch 88 (.branch 87 (.leaf 682548480) (.leaf 669330594)) (.branch 89 (.leaf 656389411) (.leaf 643718170)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 631310320) (.branch 92 (.leaf 619159511) (.leaf 607259585))) (.branch 95 (.branch 94 (.leaf 595604570) (.leaf 584188673)) (.branch 96 (.leaf 573006271) (.leaf 562051908)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 551320283) (.leaf 540806253)) (.branch 100 (.leaf 530504818) (.leaf 520411121))) (.branch 103 (.branch 102 (.leaf 510520442) (.leaf 500828192)) (.branch 104 (.leaf 491329911) (.leaf 482021257))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 472898011) (.leaf 463956065)) (.branch 108 (.leaf 455191422) (.leaf 446600191))) (.branch 111 (.branch 110 (.leaf 438178584) (.leaf 429922912)) (.branch 112 (.leaf 421829581) (.leaf 413895091)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 406116031) (.leaf 398489078)) (.branch 116 (.leaf 391010991) (.leaf 383678610))) (.branch 119 (.branch 118 (.leaf 376488857) (.leaf 369438726)) (.branch 120 (.leaf 362525288) (.leaf 355745683)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 612).prefactor = (1152508401404431/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 612).cutoff/(generalMeanRows 612).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 612).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 612).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 612).q*(generalMeanRows 612).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 612).q*(generalMeanRows 612).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 612).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 612

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 612).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 612).criticalRate j.val*(generalMeanRows 612).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 612).c*(generalMeanRows 612).criticalPoint j.val)).2-
      (generalMeanRows 612).J/2-(generalMeanRows 612).error (generalMeanGrid j.val)+
      (generalMeanRows 612).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 612).c)).2-
      (generalMeanRows 612).J/2-(generalMeanRows 612).error 4 := by
  have he : (generalMeanRows 612).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 612) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 612)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0612

/-! Kernel-checked entropy margins for general spectral rectangle 613. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0613
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5231679241) (.branch 2 (.leaf 5064017752) (.leaf 4903740800))) (.branch 5 (.branch 4 (.leaf 4750424728) (.leaf 4603675992)) (.branch 6 (.leaf 4463128526) (.leaf 4328441396)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4199296700) (.leaf 4075397677)) (.branch 10 (.leaf 3956467014) (.leaf 3842245308))) (.branch 13 (.branch 12 (.leaf 3732489682) (.leaf 3626972528)) (.branch 14 (.leaf 3525480362) (.leaf 3427812789))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3333781547) (.branch 17 (.leaf 3243209647) (.leaf 3155930574))) (.branch 20 (.branch 19 (.leaf 3071787562) (.leaf 2990632925)) (.branch 21 (.leaf 2912327443) (.leaf 2836739793)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2763746031) (.leaf 2693229108)) (.branch 25 (.leaf 2625078423) (.leaf 2559189414))) (.branch 28 (.branch 27 (.leaf 2495463175) (.leaf 2433806097)) (.branch 29 (.leaf 2374129549) (.leaf 2316349562)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2260386553) (.branch 32 (.leaf 2206165054) (.leaf 2153613471))) (.branch 35 (.branch 34 (.leaf 2102663852) (.leaf 2053251670)) (.branch 36 (.leaf 2005315630) (.leaf 1958797474)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1913641814) (.leaf 1869795960)) (.branch 40 (.leaf 1827209777) (.leaf 1785835532))) (.branch 43 (.branch 42 (.leaf 1745627767) (.leaf 1706543169)) (.branch 44 (.leaf 1668540456) (.leaf 1631580259))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1595625027) (.branch 47 (.leaf 1560638922) (.leaf 1526587730))) (.branch 50 (.branch 49 (.leaf 1493438777) (.leaf 1461160843)) (.branch 51 (.leaf 1429724088) (.leaf 1399099981)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1369261230) (.leaf 1340181721)) (.branch 55 (.leaf 1311836453) (.leaf 1284201487))) (.branch 58 (.branch 57 (.leaf 1257253890) (.leaf 1230971682)) (.branch 59 (.leaf 1205333792) (.leaf 1180320012))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1155910954) (.branch 62 (.leaf 1132088010) (.leaf 1108833313))) (.branch 65 (.branch 64 (.leaf 1086129704) (.leaf 1063960696)) (.branch 66 (.leaf 1042310441) (.leaf 1021163703)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1000505825) (.leaf 980322707)) (.branch 70 (.leaf 960600773) (.leaf 941326956))) (.branch 73 (.branch 72 (.leaf 922488666) (.leaf 904073774)) (.branch 74 (.leaf 886070588) (.leaf 868467835))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 851254643) (.branch 77 (.leaf 834420521) (.leaf 817955343))) (.branch 80 (.branch 79 (.leaf 801849333) (.leaf 786093049)) (.branch 81 (.leaf 770677370) (.leaf 755593480)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 740832857) (.leaf 726387259)) (.branch 85 (.leaf 712248714) (.leaf 698409508))) (.branch 88 (.branch 87 (.leaf 684862174) (.leaf 671599483)) (.branch 89 (.leaf 658614432) (.leaf 645900238)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 633450328) (.branch 92 (.leaf 621258330) (.leaf 609318066))) (.branch 95 (.branch 94 (.leaf 597623543) (.leaf 586168949)) (.branch 96 (.leaf 574948641) (.leaf 563957144)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 553189142) (.leaf 542639471)) (.branch 100 (.leaf 532303116) (.leaf 522175204))) (.branch 103 (.branch 102 (.leaf 512250998) (.leaf 502525894)) (.branch 104 (.leaf 492995415) (.leaf 483655207))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 474501035) (.leaf 465528778)) (.branch 108 (.leaf 456734425) (.leaf 448114071))) (.branch 111 (.branch 110 (.leaf 439663917) (.leaf 431380259)) (.branch 112 (.leaf 423259494) (.leaf 415298107)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 407492679) (.leaf 399839871)) (.branch 116 (.leaf 392336435) (.leaf 384979199))) (.branch 119 (.branch 118 (.leaf 377765074) (.leaf 370691045)) (.branch 120 (.leaf 363754172) (.leaf 356951586)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 613).prefactor = (2312830320699387/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 613).cutoff/(generalMeanRows 613).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 613).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 613).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 613).q*(generalMeanRows 613).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 613).q*(generalMeanRows 613).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 613).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 613

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 613).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 613).criticalRate j.val*(generalMeanRows 613).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 613).c*(generalMeanRows 613).criticalPoint j.val)).2-
      (generalMeanRows 613).J/2-(generalMeanRows 613).error (generalMeanGrid j.val)+
      (generalMeanRows 613).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 613).c)).2-
      (generalMeanRows 613).J/2-(generalMeanRows 613).error 4 := by
  have he : (generalMeanRows 613).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 613) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 613)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0613

/-! Kernel-checked entropy margins for general spectral rectangle 614. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0614
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4932051882) (.branch 2 (.leaf 4760142620) (.leaf 4595956528))) (.branch 5 (.branch 4 (.leaf 4439054432) (.leaf 4289028102)) (.branch 6 (.leaf 4145497552) (.leaf 4008108634)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3876530880) (.leaf 3750455570)) (.branch 10 (.leaf 3629593990) (.leaf 3513675864))) (.branch 13 (.branch 12 (.leaf 3402447930) (.leaf 3295672653)) (.branch 14 (.leaf 3193127055) (.leaf 3094601651))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2999899473) (.branch 17 (.leaf 2908835188) (.leaf 2821234280))) (.branch 20 (.branch 19 (.leaf 2736932304) (.leaf 2655774206)) (.branch 21 (.leaf 2577613690) (.leaf 2502312636)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2429740570) (.leaf 2359774166)) (.branch 25 (.leaf 2292296790) (.leaf 2227198076))) (.branch 28 (.branch 27 (.leaf 2164373538) (.leaf 2103724202)) (.branch 29 (.leaf 2045156269) (.leaf 1988580805)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1933913445) (.branch 32 (.leaf 1881074120) (.leaf 1829986809))) (.branch 35 (.branch 34 (.leaf 1780579298) (.leaf 1732782961)) (.branch 36 (.leaf 1686532554) (.leaf 1641766021)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1598424317) (.leaf 1556451235)) (.branch 40 (.leaf 1515793252) (.leaf 1476399379))) (.branch 43 (.branch 42 (.leaf 1438221021) (.leaf 1401211848)) (.branch 44 (.leaf 1365327675) (.leaf 1330526342))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1296767613) (.branch 47 (.leaf 1264013065) (.leaf 1232226002))) (.branch 50 (.branch 49 (.leaf 1201371361) (.leaf 1171415625)) (.branch 51 (.leaf 1142326749) (.leaf 1114074080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1086628289) (.leaf 1059961303)) (.branch 55 (.leaf 1034046242) (.leaf 1008857360))) (.branch 58 (.branch 57 (.leaf 984369991) (.leaf 960560492)) (.branch 59 (.leaf 937406194) (.leaf 914885358))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 892977127) (.branch 62 (.leaf 871661484) (.leaf 850919213))) (.branch 65 (.branch 64 (.leaf 830731861) (.leaf 811081700)) (.branch 66 (.leaf 791951699) (.leaf 773325483)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 755187310) (.leaf 737522039)) (.branch 70 (.leaf 720315104) (.leaf 703552484))) (.branch 73 (.branch 72 (.leaf 687220685) (.leaf 671306711)) (.branch 74 (.leaf 655798044) (.leaf 640682624))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 625948826) (.branch 77 (.leaf 611585444) (.leaf 597581673))) (.branch 80 (.branch 79 (.leaf 583927087) (.leaf 570611630)) (.branch 81 (.leaf 557625596) (.leaf 544959612)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 532604631) (.leaf 520551912)) (.branch 85 (.leaf 508793011) (.leaf 497319767))) (.branch 88 (.branch 87 (.leaf 486124293) (.leaf 475198961)) (.branch 89 (.leaf 464536394) (.leaf 454129458)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 443971248) (.branch 92 (.leaf 434055082) (.leaf 424374491))) (.branch 95 (.branch 94 (.leaf 414923211) (.leaf 405695177)) (.branch 96 (.leaf 396684511) (.leaf 387885521)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 379292687) (.leaf 370900661)) (.branch 100 (.leaf 362704257) (.leaf 354698446))) (.branch 103 (.branch 102 (.leaf 346878348) (.leaf 339239232)) (.branch 104 (.leaf 331776506) (.leaf 324485711))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 317362522) (.leaf 310402738)) (.branch 108 (.leaf 303602281) (.leaf 296957188))) (.branch 111 (.branch 110 (.leaf 290463610) (.leaf 284117808)) (.branch 112 (.leaf 277916149) (.leaf 271855101)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265931230) (.leaf 260141199)) (.branch 116 (.leaf 254481762) (.leaf 248949762))) (.branch 119 (.branch 118 (.leaf 243542128) (.leaf 238255873)) (.branch 120 (.leaf 233088092) (.leaf 228035955)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 614).prefactor = (47645306888287/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 614).cutoff/(generalMeanRows 614).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 614).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 614).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 614).q*(generalMeanRows 614).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 614).q*(generalMeanRows 614).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 614).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 614

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 614).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 614).criticalRate j.val*(generalMeanRows 614).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 614).c*(generalMeanRows 614).criticalPoint j.val)).2-
      (generalMeanRows 614).J/2-(generalMeanRows 614).error (generalMeanGrid j.val)+
      (generalMeanRows 614).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 614).c)).2-
      (generalMeanRows 614).J/2-(generalMeanRows 614).error 4 := by
  have he : (generalMeanRows 614).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 614) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 614)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0614

/-! Kernel-checked entropy margins for general spectral rectangle 615. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0615
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4949229531) (.branch 2 (.leaf 4776721533) (.leaf 4611963604))) (.branch 5 (.branch 4 (.leaf 4454515039) (.leaf 4303966189)) (.branch 6 (.leaf 4159935742) (.leaf 4022068318)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3890032296) (.leaf 3763517883)) (.branch 10 (.leaf 3642235360) (.leaf 3525913507))) (.branch 13 (.branch 12 (.leaf 3414298182) (.leaf 3307151021)) (.branch 14 (.leaf 3204248272) (.leaf 3105379717))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3010347705) (.branch 17 (.leaf 2918966256) (.leaf 2831060245))) (.branch 20 (.branch 19 (.leaf 2746464657) (.leaf 2665023897)) (.branch 21 (.leaf 2586591159) (.leaf 2511027842)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2438203018) (.leaf 2367992930)) (.branch 25 (.leaf 2300280540) (.leaf 2234955096))) (.branch 28 (.branch 27 (.leaf 2171911749) (.leaf 2111051180)) (.branch 29 (.leaf 2052279263) (.leaf 1995506755)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1940648996) (.branch 32 (.leaf 1887625639) (.leaf 1836360398))) (.branch 35 (.branch 34 (.leaf 1786780807) (.leaf 1738818002)) (.branch 36 (.leaf 1692406511) (.leaf 1647484063)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1603991406) (.leaf 1561872138)) (.branch 40 (.leaf 1521072549) (.leaf 1481541472))) (.branch 43 (.branch 42 (.leaf 1443230144) (.leaf 1406092073)) (.branch 44 (.leaf 1370082921) (.leaf 1335160380))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1301284073) (.branch 47 (.leaf 1268415446) (.leaf 1236517673))) (.branch 50 (.branch 49 (.leaf 1205555570) (.leaf 1175495502)) (.branch 51 (.leaf 1146305314) (.leaf 1117954245)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1090412864) (.leaf 1063653000)) (.branch 55 (.leaf 1037647681) (.leaf 1012371070))) (.branch 58 (.branch 57 (.leaf 987798415) (.leaf 963905990)) (.branch 59 (.leaf 940671049) (.leaf 918071777))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 896087242) (.branch 62 (.leaf 874697360) (.leaf 853882846))) (.branch 65 (.branch 64 (.leaf 833625184) (.leaf 813906585)) (.branch 66 (.leaf 794709956) (.leaf 776018868)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 757817522) (.leaf 740090726)) (.branch 70 (.leaf 722823861) (.leaf 706002860))) (.branch 73 (.branch 72 (.leaf 689614179) (.leaf 673644779)) (.branch 74 (.leaf 658082097) (.leaf 642914032))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 628128918) (.branch 77 (.leaf 613715511) (.leaf 599662966))) (.branch 80 (.branch 79 (.leaf 585960824) (.leaf 572598991)) (.branch 81 (.leaf 559567728) (.leaf 546857630)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 534459618) (.leaf 522364921)) (.branch 85 (.leaf 510565066) (.leaf 499051863))) (.branch 88 (.branch 87 (.leaf 487817396) (.leaf 476854012)) (.branch 89 (.leaf 466154310) (.leaf 455711128)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 445517538) (.branch 92 (.leaf 435566835) (.leaf 425852528))) (.branch 95 (.branch 94 (.leaf 416368331) (.leaf 407108156)) (.branch 96 (.leaf 398066108) (.leaf 389236472)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 380613711) (.leaf 372192457)) (.branch 100 (.leaf 363967506) (.leaf 355933811))) (.branch 103 (.branch 102 (.leaf 348086477) (.leaf 340420755)) (.branch 104 (.leaf 332932037) (.leaf 325615849))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 318467851) (.leaf 311483828)) (.branch 108 (.leaf 304659685) (.leaf 297991448))) (.branch 111 (.branch 110 (.leaf 291475254) (.leaf 285107351)) (.branch 112 (.leaf 278884093) (.leaf 272801935)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 266857432) (.leaf 261047235)) (.branch 116 (.leaf 255368086) (.leaf 249816819))) (.branch 119 (.branch 118 (.leaf 244390351) (.leaf 239085685)) (.branch 120 (.leaf 233899905) (.leaf 228830173)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 615).prefactor = (478112488488809/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 615).cutoff/(generalMeanRows 615).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 615).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 615).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 615).q*(generalMeanRows 615).c/2-2 = (1691/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable175.value]
    have hcontinuation : (generalMeanRows 615).q*(generalMeanRows 615).cutoff/2-2 = (2690/1287:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable203.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 615).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 615

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 615).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 615).criticalRate j.val*(generalMeanRows 615).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 615).c*(generalMeanRows 615).criticalPoint j.val)).2-
      (generalMeanRows 615).J/2-(generalMeanRows 615).error (generalMeanGrid j.val)+
      (generalMeanRows 615).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 615).c)).2-
      (generalMeanRows 615).J/2-(generalMeanRows 615).error 4 := by
  have he : (generalMeanRows 615).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 615) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 615)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0615

/-! Kernel-checked entropy margins for general spectral rectangle 616. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0616
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5249413524) (.branch 2 (.leaf 5081183698) (.leaf 4920363440))) (.branch 5 (.branch 4 (.leaf 4766527660) (.leaf 4619281477)) (.branch 6 (.leaf 4478257585) (.leaf 4343113894)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4213531425) (.leaf 4089212411)) (.branch 10 (.leaf 3969878598) (.leaf 3855269704))) (.branch 13 (.branch 12 (.leaf 3745142030) (.leaf 3639267195)) (.branch 14 (.leaf 3537430993) (.leaf 3439432347))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3345082359) (.branch 17 (.leaf 3254203439) (.leaf 3166628509))) (.branch 20 (.branch 19 (.leaf 3082200270) (.leaf 3000770536)) (.branch 21 (.leaf 2922199615) (.leaf 2846355739)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2773114544) (.leaf 2702358583)) (.branch 25 (.leaf 2633976882) (.leaf 2567864524))) (.branch 28 (.branch 27 (.leaf 2503922265) (.leaf 2442056184)) (.branch 29 (.leaf 2382177344) (.leaf 2324201496)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2268048784) (.branch 32 (.leaf 2213643486) (.leaf 2160913764))) (.branch 35 (.branch 34 (.leaf 2109791436) (.leaf 2060211758)) (.branch 36 (.leaf 2012113224) (.leaf 1965437382)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1920128653) (.leaf 1876134172)) (.branch 40 (.leaf 1833403630) (.leaf 1791889135))) (.branch 43 (.branch 42 (.leaf 1751545075) (.leaf 1712327989)) (.branch 44 (.leaf 1674196454) (.leaf 1637110970))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1601033857) (.branch 47 (.leaf 1565929156) (.leaf 1531762539))) (.branch 50 (.branch 49 (.leaf 1498501218) (.leaf 1466113868)) (.branch 51 (.leaf 1434570549) (.leaf 1403842633)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1373902735) (.leaf 1344724652)) (.branch 55 (.leaf 1316283300) (.leaf 1288554658))) (.branch 58 (.branch 57 (.leaf 1261515714) (.leaf 1235144415)) (.branch 59 (.leaf 1209419618) (.leaf 1184321046))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1159829247) (.branch 62 (.leaf 1135925548) (.leaf 1112592022))) (.branch 65 (.branch 64 (.leaf 1089811453) (.leaf 1067567297)) (.branch 66 (.leaf 1045843652) (.leaf 1024625231)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1003897328) (.leaf 983645793)) (.branch 70 (.leaf 963857006) (.leaf 944517855))) (.branch 73 (.branch 72 (.leaf 925615707) (.leaf 907138392)) (.branch 74 (.leaf 889074179) (.leaf 871411757))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 854140216) (.branch 77 (.leaf 837249030) (.leaf 820728038))) (.branch 80 (.branch 79 (.leaf 804567432) (.leaf 788757738)) (.branch 81 (.leaf 773289803) (.leaf 758154782)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 743344123) (.leaf 728849558)) (.branch 85 (.leaf 714663086) (.leaf 700776968))) (.branch 88 (.branch 87 (.leaf 687183712) (.leaf 673876062)) (.branch 89 (.leaf 660846995) (.leaf 648089703)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 635597590) (.branch 92 (.leaf 623364264) (.leaf 611383525))) (.branch 95 (.branch 94 (.leaf 599649360) (.leaf 588155937)) (.branch 96 (.leaf 576897595) (.leaf 565868839)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 555064336) (.leaf 544478904)) (.branch 100 (.leaf 534107511) (.leaf 523945267))) (.branch 103 (.branch 102 (.leaf 513987420) (.leaf 504229350)) (.branch 104 (.leaf 494666565) (.leaf 485294696))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 476109493) (.leaf 467106822)) (.branch 108 (.leaf 458282657) (.leaf 449633083))) (.branch 111 (.branch 110 (.leaf 441154284) (.leaf 432842547)) (.branch 112 (.leaf 424694253) (.leaf 416705880)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 408873992) (.leaf 401195244)) (.branch 116 (.leaf 393666372) (.leaf 386284197))) (.branch 119 (.branch 118 (.leaf 379045618) (.leaf 371947609)) (.branch 120 (.leaf 364987221) (.leaf 358161576)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 616).prefactor = (580167581189429/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 616).cutoff/(generalMeanRows 616).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 616).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 616).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 616).q*(generalMeanRows 616).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 616).q*(generalMeanRows 616).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 616).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 616

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 616).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 616).criticalRate j.val*(generalMeanRows 616).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 616).c*(generalMeanRows 616).criticalPoint j.val)).2-
      (generalMeanRows 616).J/2-(generalMeanRows 616).error (generalMeanGrid j.val)+
      (generalMeanRows 616).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 616).c)).2-
      (generalMeanRows 616).J/2-(generalMeanRows 616).error 4 := by
  have he : (generalMeanRows 616).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 616) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 616)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0616

/-! Kernel-checked entropy margins for general spectral rectangle 617. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0617
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5267207922) (.branch 2 (.leaf 5098407832) (.leaf 4937042429))) (.branch 5 (.branch 4 (.leaf 4782685178) (.leaf 4634939861)) (.branch 6 (.leaf 4493437928) (.leaf 4357836129)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4227814402) (.leaf 4103073973)) (.branch 10 (.leaf 3983335644) (.leaf 3868338251))) (.branch 13 (.branch 12 (.leaf 3757837267) (.leaf 3651603539)) (.branch 14 (.leaf 3549422133) (.leaf 3451091293))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3356421479) (.branch 17 (.leaf 3265234499) (.leaf 3177362708))) (.branch 20 (.branch 19 (.leaf 3092648275) (.leaf 3010942512)) (.branch 21 (.leaf 2932105252) (.leaf 2856004281)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2782514814) (.leaf 2711519005)) (.branch 25 (.leaf 2642905505) (.leaf 2576569039))) (.branch 28 (.branch 27 (.leaf 2512410030) (.leaf 2450334236)) (.branch 29 (.leaf 2390252420) (.leaf 2332080046)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2275736988) (.branch 32 (.leaf 2221147267) (.leaf 2168238803))) (.branch 35 (.branch 34 (.leaf 2116943181) (.leaf 2067195438)) (.branch 36 (.leaf 2018933861) (.leaf 1972099798)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1926637482) (.leaf 1882493869)) (.branch 40 (.leaf 1839618479) (.leaf 1797963259))) (.branch 43 (.branch 42 (.leaf 1757482441) (.leaf 1718132417)) (.branch 44 (.leaf 1679871625) (.leaf 1642660429))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1606461022) (.branch 47 (.leaf 1571237324) (.leaf 1536954889))) (.branch 50 (.branch 49 (.leaf 1503580819) (.leaf 1471083683)) (.branch 51 (.leaf 1439433439) (.leaf 1408601362)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1378559974) (.leaf 1349282984)) (.branch 55 (.leaf 1320745221) (.leaf 1292922585))) (.branch 58 (.branch 57 (.leaf 1265791984) (.leaf 1239331292)) (.branch 59 (.leaf 1213519294) (.leaf 1188335643))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1163760822) (.branch 62 (.leaf 1139776094) (.leaf 1116363473))) (.branch 65 (.branch 64 (.leaf 1093505683) (.leaf 1071186123)) (.branch 66 (.leaf 1049388840) (.leaf 1028098493)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1007300327) (.leaf 986980143)) (.branch 70 (.leaf 967124277) (.leaf 947719570))) (.branch 73 (.branch 72 (.leaf 928753348) (.leaf 910213399)) (.branch 74 (.leaf 892087952) (.leaf 874365658))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 857035570) (.branch 77 (.leaf 840087126) (.leaf 823510132))) (.branch 80 (.branch 79 (.leaf 807294745) (.leaf 791431459)) (.branch 81 (.leaf 775911091) (.leaf 760724766)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 745863902) (.leaf 731320203)) (.branch 85 (.leaf 717085643) (.leaf 703152454))) (.branch 88 (.branch 87 (.leaf 689513119) (.leaf 676160359)) (.branch 89 (.leaf 663087126) (.leaf 650286589)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 637752131) (.branch 92 (.leaf 625477337) (.leaf 613455986))) (.branch 95 (.branch 94 (.leaf 601682045) (.leaf 590149661)) (.branch 96 (.leaf 578853155) (.leaf 567787015)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 556945886) (.leaf 546324572)) (.branch 100 (.leaf 535918022) (.leaf 525721330))) (.branch 103 (.branch 102 (.leaf 515729728) (.leaf 505938580)) (.branch 104 (.leaf 496343379) (.leaf 486939742))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 477723403) (.leaf 468690215)) (.branch 108 (.leaf 459836138) (.leaf 451157244))) (.branch 111 (.branch 110 (.leaf 442649703) (.leaf 434309791)) (.branch 112 (.leaf 426133877) (.leaf 418118424)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 410259988) (.leaf 402555210)) (.branch 116 (.leaf 395000818) (.leaf 387593619))) (.branch 119 (.branch 118 (.leaf 380330502) (.leaf 373208432)) (.branch 120 (.leaf 366224450) (.leaf 359375668)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 617).prefactor = (465707380953267/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 617).cutoff/(generalMeanRows 617).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 617).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 617).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 617).q*(generalMeanRows 617).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 617).q*(generalMeanRows 617).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 617).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 617

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 617).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 617).criticalRate j.val*(generalMeanRows 617).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 617).c*(generalMeanRows 617).criticalPoint j.val)).2-
      (generalMeanRows 617).J/2-(generalMeanRows 617).error (generalMeanGrid j.val)+
      (generalMeanRows 617).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 617).c)).2-
      (generalMeanRows 617).J/2-(generalMeanRows 617).error 4 := by
  have he : (generalMeanRows 617).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 617) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 617)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0617

/-! Kernel-checked entropy margins for general spectral rectangle 618. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0618
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5027866391) (.branch 2 (.leaf 4854915542) (.leaf 4689717821))) (.branch 5 (.branch 4 (.leaf 4531831147) (.leaf 4380844652)) (.branch 6 (.leaf 4236375966) (.leaf 4098068782)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3965590684) (.leaf 3838631191)) (.branch 10 (.leaf 3716900000) (.leaf 3600125404))) (.branch 13 (.branch 12 (.leaf 3488052854) (.leaf 3380443658)) (.branch 14 (.leaf 3277073801) (.leaf 3177732871))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3082223073) (.branch 17 (.leaf 2990358335) (.leaf 2901963486))) (.branch 20 (.branch 19 (.leaf 2816873505) (.leaf 2734932826)) (.branch 21 (.leaf 2655994707) (.leaf 2579920637)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2506579805) (.leaf 2435848591)) (.branch 25 (.leaf 2367610115) (.leaf 2301753801))) (.branch 28 (.branch 27 (.leaf 2238174987) (.leaf 2176774557)) (.branch 29 (.leaf 2117458598) (.leaf 2060138086)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2004728590) (.branch 32 (.leaf 1951149998) (.leaf 1899326260))) (.branch 35 (.branch 34 (.leaf 1849185154) (.leaf 1800658058)) (.branch 36 (.leaf 1753679745) (.leaf 1708188188)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1664124382) (.leaf 1621432166)) (.branch 40 (.leaf 1580058072) (.leaf 1539951172))) (.branch 43 (.branch 42 (.leaf 1501062939) (.leaf 1463347113)) (.branch 44 (.leaf 1426759584) (.leaf 1391258270))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1356803013) (.branch 47 (.leaf 1323355474) (.leaf 1290879038))) (.branch 50 (.branch 49 (.leaf 1259338724) (.leaf 1228701101)) (.branch 51 (.leaf 1198934204) (.leaf 1170007463)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1141891630) (.leaf 1114558712)) (.branch 55 (.leaf 1087981908) (.leaf 1062135548))) (.branch 58 (.branch 57 (.leaf 1036995039) (.leaf 1012536811)) (.branch 59 (.leaf 988738267) (.leaf 965577734))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 943034420) (.branch 62 (.leaf 921088370) (.leaf 899720429))) (.branch 65 (.branch 64 (.leaf 878912200) (.leaf 858646011)) (.branch 66 (.leaf 838904880) (.leaf 819672483)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 800933122) (.leaf 782671700)) (.branch 70 (.leaf 764873690) (.leaf 747525108))) (.branch 73 (.branch 72 (.leaf 730612496) (.leaf 714122887)) (.branch 74 (.leaf 698043795) (.leaf 682363183))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667069451) (.branch 77 (.leaf 652151415) (.leaf 637598285))) (.branch 80 (.branch 79 (.leaf 623399653) (.leaf 609545476)) (.branch 81 (.leaf 596026058) (.leaf 582832035)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 569954366) (.leaf 557384314)) (.branch 85 (.leaf 545113436) (.leaf 533133572))) (.branch 88 (.branch 87 (.leaf 521436830) (.leaf 510015580)) (.branch 89 (.leaf 498862438) (.leaf 487970261)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 477332134) (.branch 92 (.leaf 466941364) (.leaf 456791467))) (.branch 95 (.branch 94 (.leaf 446876165) (.leaf 437189376)) (.branch 96 (.leaf 427725204) (.leaf 418477937)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 409442035) (.leaf 400612126)) (.branch 100 (.leaf 391983001) (.leaf 383549606))) (.branch 103 (.branch 102 (.leaf 375307037) (.leaf 367250532)) (.branch 104 (.leaf 359375473) (.leaf 351677373))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 344151876) (.leaf 336794749)) (.branch 108 (.leaf 329601882) (.leaf 322569280))) (.branch 111 (.branch 110 (.leaf 315693061) (.leaf 308969451)) (.branch 112 (.leaf 302394782) (.leaf 295965487)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 289678095) (.leaf 283529233)) (.branch 116 (.leaf 277515617) (.leaf 271634053))) (.branch 119 (.branch 118 (.leaf 265881432) (.leaf 260254728)) (.branch 120 (.leaf 254750996) (.leaf 249367369)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 618).prefactor = (958784880920799/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 618).cutoff/(generalMeanRows 618).c)).2 =
    (93274744152067/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 618).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 618).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 618).q*(generalMeanRows 618).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 618).q*(generalMeanRows 618).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 618).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 618

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 618).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 618).criticalRate j.val*(generalMeanRows 618).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 618).c*(generalMeanRows 618).criticalPoint j.val)).2-
      (generalMeanRows 618).J/2-(generalMeanRows 618).error (generalMeanGrid j.val)+
      (generalMeanRows 618).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 618).c)).2-
      (generalMeanRows 618).J/2-(generalMeanRows 618).error 4 := by
  have he : (generalMeanRows 618).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 618) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 618)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0618

/-! Kernel-checked entropy margins for general spectral rectangle 619. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0619
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5233984799) (.branch 2 (.leaf 5058902058) (.leaf 4891608202))) (.branch 5 (.branch 4 (.leaf 4731658490) (.leaf 4578639650)) (.branch 6 (.leaf 4432167125) (.leaf 4291882626)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4157451938) (.leaf 4028562950)) (.branch 10 (.leaf 3904923884) (.leaf 3786261695))) (.branch 13 (.branch 12 (.leaf 3672320623) (.leaf 3562860885)) (.branch 14 (.leaf 3457657478) (.leaf 3356499101))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3259187156) (.branch 17 (.leaf 3165534853) (.leaf 3075366378))) (.branch 20 (.branch 19 (.leaf 2988516129) (.leaf 2904828029)) (.branch 21 (.leaf 2824154876) (.leaf 2746357754)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2671305492) (.leaf 2598874159)) (.branch 25 (.leaf 2528946596) (.leaf 2461411988))) (.branch 28 (.branch 27 (.leaf 2396165469) (.leaf 2333107744)) (.branch 29 (.leaf 2272144752) (.leaf 2213187343)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2156150984) (.branch 32 (.leaf 2100955479) (.leaf 2047524717))) (.branch 35 (.branch 34 (.leaf 1995786424) (.leaf 1945671945)) (.branch 36 (.leaf 1897116035) (.leaf 1850056656)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1804434804) (.leaf 1760194331)) (.branch 40 (.leaf 1717281785) (.leaf 1675646264))) (.branch 43 (.branch 42 (.leaf 1635239271) (.leaf 1596014584)) (.branch 44 (.leaf 1557928133) (.leaf 1520937880))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1485003715) (.branch 47 (.leaf 1450087346) (.leaf 1416152212))) (.branch 50 (.branch 49 (.leaf 1383163382) (.leaf 1351087478)) (.branch 51 (.leaf 1319892590) (.leaf 1289548199)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1260025110) (.leaf 1231295382)) (.branch 55 (.leaf 1203332264) (.leaf 1176110137))) (.branch 58 (.branch 57 (.leaf 1149604455) (.leaf 1123791693)) (.branch 59 (.leaf 1098649299) (.leaf 1074155643))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050289970) (.branch 62 (.leaf 1027032365) (.leaf 1004363707))) (.branch 65 (.branch 64 (.leaf 982265631) (.leaf 960720494)) (.branch 66 (.leaf 939711341) (.leaf 919221873)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 899236413) (.leaf 879739882)) (.branch 70 (.leaf 860717768) (.leaf 842156103))) (.branch 73 (.branch 72 (.leaf 824041433) (.leaf 806360804)) (.branch 74 (.leaf 789101729) (.leaf 772252175))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 755800541) (.branch 77 (.leaf 739735635) (.leaf 724046664))) (.branch 80 (.branch 79 (.leaf 708723209) (.leaf 693755213)) (.branch 81 (.leaf 679132965) (.leaf 664847084)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 650888508) (.leaf 637248477)) (.branch 85 (.leaf 623918525) (.leaf 610890461))) (.branch 88 (.branch 87 (.leaf 598156365) (.leaf 585708573)) (.branch 89 (.leaf 573539668) (.leaf 561642470)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 550010025) (.branch 92 (.leaf 538635598) (.leaf 527512664))) (.branch 95 (.branch 94 (.leaf 516634901) (.leaf 505996177)) (.branch 96 (.leaf 495590552) (.leaf 485412260)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 475455711) (.leaf 465715480)) (.branch 100 (.leaf 456186303) (.leaf 446863069))) (.branch 103 (.branch 102 (.leaf 437740816) (.leaf 428814725)) (.branch 104 (.leaf 420080115) (.leaf 411532438))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403167275) (.leaf 394980330)) (.branch 108 (.leaf 386967426) (.leaf 379124504))) (.branch 111 (.branch 110 (.leaf 371447614) (.leaf 363932913)) (.branch 112 (.leaf 356576665) (.leaf 349375233)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342325076) (.leaf 335422748)) (.branch 116 (.leaf 328664895) (.leaf 322048249))) (.branch 119 (.branch 118 (.leaf 315569629) (.leaf 309225935)) (.branch 120 (.leaf 303014147) (.leaf 296931323)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 619).prefactor = (4827100176226049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 619).cutoff/(generalMeanRows 619).c)).2 =
    (77616106044777/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 619).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 619).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 619).q*(generalMeanRows 619).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    have hcontinuation : (generalMeanRows 619).q*(generalMeanRows 619).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 619).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 619

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 619).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 619).criticalRate j.val*(generalMeanRows 619).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 619).c*(generalMeanRows 619).criticalPoint j.val)).2-
      (generalMeanRows 619).J/2-(generalMeanRows 619).error (generalMeanGrid j.val)+
      (generalMeanRows 619).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 619).c)).2-
      (generalMeanRows 619).J/2-(generalMeanRows 619).error 4 := by
  have he : (generalMeanRows 619).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 619) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 619)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0619

/-! Kernel-checked entropy margins for general spectral rectangle 620. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0620
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5214258259) (.branch 2 (.leaf 5044649154) (.leaf 4882535750))) (.branch 5 (.branch 4 (.leaf 4727488489) (.leaf 4579108316)) (.branch 6 (.leaf 4437024009) (.leaf 4300889808)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4170383280) (.leaf 4045203411)) (.branch 10 (.leaf 3925068888) (.leaf 3809716543))) (.branch 13 (.branch 12 (.leaf 3698899952) (.leaf 3592388159)) (.branch 14 (.leaf 3489964521) (.leaf 3391425655))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296580473) (.branch 17 (.leaf 3205249312) (.leaf 3117263121))) (.branch 20 (.branch 19 (.leaf 3032462731) (.leaf 2950698176)) (.branch 21 (.leaf 2871828068) (.leaf 2795719027)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2722245151) (.leaf 2651287530)) (.branch 25 (.leaf 2582733789) (.leaf 2516477679))) (.branch 28 (.branch 27 (.leaf 2452418681) (.leaf 2390461656)) (.branch 29 (.leaf 2330516505) (.leaf 2272497864)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2216324813) (.branch 32 (.leaf 2161920611) (.leaf 2109212445))) (.branch 35 (.branch 34 (.leaf 2058131197) (.leaf 2008611226)) (.branch 36 (.leaf 1960590171) (.leaf 1914008754)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1868810606) (.leaf 1824942106)) (.branch 40 (.leaf 1782352218) (.leaf 1740992351))) (.branch 43 (.branch 42 (.leaf 1700816223) (.leaf 1661779731)) (.branch 44 (.leaf 1623840832) (.leaf 1586959434))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1551097285) (.branch 47 (.leaf 1516217877) (.leaf 1482286356))) (.branch 50 (.branch 49 (.leaf 1449269427) (.leaf 1417135277)) (.branch 51 (.leaf 1385853499) (.leaf 1355395011)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1325731998) (.leaf 1296837838)) (.branch 55 (.leaf 1268687045) (.leaf 1241255214))) (.branch 58 (.branch 57 (.leaf 1214518961) (.leaf 1188455876)) (.branch 59 (.leaf 1163044471) (.leaf 1138264140))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1114095111) (.branch 62 (.leaf 1090518406) (.leaf 1067515803))) (.branch 65 (.branch 64 (.leaf 1045069801) (.leaf 1023163585)) (.branch 66 (.leaf 1001780990) (.leaf 980906476)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 960525095) (.leaf 940622462)) (.branch 70 (.leaf 921184733) (.leaf 902198580))) (.branch 73 (.branch 72 (.leaf 883651162) (.leaf 865530109)) (.branch 74 (.leaf 847823497) (.leaf 830519831))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 813608024) (.branch 77 (.leaf 797077379) (.leaf 780917571))) (.branch 80 (.branch 79 (.leaf 765118634) (.leaf 749670943)) (.branch 81 (.leaf 734565201) (.leaf 719792422)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705343922) (.leaf 691211303)) (.branch 85 (.leaf 677386442) (.leaf 663861481))) (.branch 88 (.branch 87 (.leaf 650628815) (.leaf 637681081)) (.branch 89 (.leaf 625011151) (.leaf 612612118)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 600477291) (.branch 92 (.leaf 588600187) (.leaf 576974519))) (.branch 95 (.branch 94 (.leaf 565594191) (.leaf 554453290)) (.branch 96 (.leaf 543546082) (.leaf 532866998)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 522410636) (.leaf 512171749)) (.branch 100 (.leaf 502145242) (.leaf 492326165))) (.branch 103 (.branch 102 (.leaf 482709711) (.leaf 473291205)) (.branch 104 (.leaf 464066104) (.leaf 455029992))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 446178572) (.leaf 437507667)) (.branch 108 (.leaf 429013210) (.leaf 420691247))) (.branch 111 (.branch 110 (.leaf 412537927) (.leaf 404549502)) (.branch 112 (.leaf 396722321) (.leaf 389052831)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381537570) (.leaf 374173165)) (.branch 116 (.leaf 366956328) (.leaf 359883858))) (.branch 119 (.branch 118 (.leaf 352952631) (.leaf 346159605)) (.branch 120 (.leaf 339501810) (.leaf 332976354)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 620).prefactor = (937740061314861/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 620).cutoff/(generalMeanRows 620).c)).2 =
    (81074405466789/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 620).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 620).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 620).q*(generalMeanRows 620).c/2-2 = (1199/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable178.value]
    have hcontinuation : (generalMeanRows 620).q*(generalMeanRows 620).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 620).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 620

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 620).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 620).criticalRate j.val*(generalMeanRows 620).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 620).c*(generalMeanRows 620).criticalPoint j.val)).2-
      (generalMeanRows 620).J/2-(generalMeanRows 620).error (generalMeanGrid j.val)+
      (generalMeanRows 620).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 620).c)).2-
      (generalMeanRows 620).J/2-(generalMeanRows 620).error 4 := by
  have he : (generalMeanRows 620).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 620) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 620)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0620

/-! Kernel-checked entropy margins for general spectral rectangle 621. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0621
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5338990755) (.branch 2 (.leaf 5167890215) (.leaf 5004325683))) (.branch 5 (.branch 4 (.leaf 4847864813) (.leaf 4698105986)) (.branch 6 (.leaf 4554675629) (.leaf 4417225814)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4285432119) (.leaf 4158991696)) (.branch 10 (.leaf 4037621543) (.leaf 3921056936))) (.branch 13 (.branch 12 (.leaf 3809050017) (.leaf 3701368509)) (.branch 14 (.leaf 3597794550) (.leaf 3498123632))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3402163634) (.branch 17 (.leaf 3309733935) (.leaf 3220664605))) (.branch 20 (.branch 19 (.leaf 3134795663) (.leaf 3051976393)) (.branch 21 (.leaf 2972064719) (.leaf 2894926625)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2820435625) (.leaf 2748472268)) (.branch 25 (.leaf 2678923685) (.leaf 2611683170))) (.branch 28 (.branch 27 (.leaf 2546649785) (.leaf 2483728006)) (.branch 29 (.leaf 2422827381) (.leaf 2363862219)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2306751303) (.branch 32 (.leaf 2251417620) (.leaf 2197788106))) (.branch 35 (.branch 34 (.leaf 2145793415) (.leaf 2095367697)) (.branch 36 (.leaf 2046448399) (.leaf 1998976069)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1952894182) (.leaf 1908148968)) (.branch 40 (.leaf 1864689262) (.leaf 1822466354))) (.branch 43 (.branch 42 (.leaf 1781433853) (.leaf 1741547557)) (.branch 44 (.leaf 1702765337) (.leaf 1665047018))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1628354276) (.branch 47 (.leaf 1592650541) (.leaf 1557900896))) (.branch 50 (.branch 49 (.leaf 1524071996) (.leaf 1491131981)) (.branch 51 (.leaf 1459050400) (.leaf 1427798135)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1397347336) (.leaf 1367671351)) (.branch 55 (.leaf 1338744669) (.leaf 1310542859))) (.branch 58 (.branch 57 (.leaf 1283042516) (.leaf 1256221210)) (.branch 59 (.leaf 1230057439) (.leaf 1204530580))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1179620847) (.branch 62 (.leaf 1155309249) (.leaf 1131577555))) (.branch 65 (.branch 64 (.leaf 1108408253) (.leaf 1085784517)) (.branch 66 (.leaf 1063690175) (.leaf 1042109678)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1021028069) (.leaf 1000430957)) (.branch 70 (.leaf 980304490) (.leaf 960635330))) (.branch 73 (.branch 72 (.leaf 941410632) (.leaf 922618016)) (.branch 74 (.leaf 904245551) (.leaf 886281733))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 868715466) (.branch 77 (.leaf 851536044) (.leaf 834733135))) (.branch 80 (.branch 79 (.leaf 818296760) (.leaf 802217286)) (.branch 81 (.leaf 786485403) (.leaf 771092114)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 756028723) (.leaf 741286819)) (.branch 85 (.leaf 726858266) (.leaf 712735192))) (.branch 88 (.branch 87 (.leaf 698909977) (.leaf 685375242)) (.branch 89 (.leaf 672123844) (.leaf 659148858)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 646443578) (.branch 92 (.leaf 634001499) (.leaf 621816318))) (.branch 95 (.branch 94 (.leaf 609881919) (.leaf 598192369)) (.branch 96 (.leaf 586741912) (.leaf 575524959)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564536085) (.leaf 553770020)) (.branch 100 (.leaf 543221648) (.leaf 532885993))) (.branch 103 (.branch 102 (.leaf 522758223) (.leaf 512833638)) (.branch 104 (.leaf 503107672) (.leaf 493575879))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 484233938) (.leaf 475077643)) (.branch 108 (.leaf 466102901) (.leaf 457305728))) (.branch 111 (.branch 110 (.leaf 448682245) (.leaf 440228674)) (.branch 112 (.leaf 431941336) (.leaf 423816647)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 415851115) (.leaf 408041334)) (.branch 116 (.leaf 400383988) (.leaf 392875842))) (.branch 119 (.branch 118 (.leaf 385513741) (.leaf 378294611)) (.branch 120 (.leaf 371215449) (.leaf 364273330)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 621).prefactor = (2360270790627219/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 621).cutoff/(generalMeanRows 621).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 621).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 621).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 621).q*(generalMeanRows 621).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 621).q*(generalMeanRows 621).cutoff/2-2 = (2009/946:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable206.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 621).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 621

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 621).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 621).criticalRate j.val*(generalMeanRows 621).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 621).c*(generalMeanRows 621).criticalPoint j.val)).2-
      (generalMeanRows 621).J/2-(generalMeanRows 621).error (generalMeanGrid j.val)+
      (generalMeanRows 621).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 621).c)).2-
      (generalMeanRows 621).J/2-(generalMeanRows 621).error 4 := by
  have he : (generalMeanRows 621).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 621) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 621)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0621

/-! Kernel-checked entropy margins for general spectral rectangle 622. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0622
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5444252245) (.branch 2 (.leaf 5264996912) (.leaf 5093712146))) (.branch 5 (.branch 4 (.leaf 4929941006) (.leaf 4773258952)) (.branch 6 (.leaf 4623271014) (.leaf 4479609270)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4341930586) (.leaf 4209914587)) (.branch 10 (.leaf 4083261831) (.leaf 3961692164))) (.branch 13 (.branch 12 (.leaf 3844943227) (.leaf 3732769104)) (.branch 14 (.leaf 3624939098) (.leaf 3521236606))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3421458109) (.branch 17 (.leaf 3325412231) (.leaf 3232918889))) (.branch 20 (.branch 19 (.leaf 3143808513) (.leaf 3057921322)) (.branch 21 (.leaf 2975106668) (.leaf 2895222425)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2818134428) (.leaf 2743715953)) (.branch 25 (.leaf 2671847242) (.leaf 2602415053))) (.branch 28 (.branch 27 (.leaf 2535312256) (.leaf 2470437445)) (.branch 29 (.leaf 2407694588) (.leaf 2346992700)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2288245532) (.branch 32 (.leaf 2231371287) (.leaf 2176292359))) (.branch 35 (.branch 34 (.leaf 2122935081) (.leaf 2071229496)) (.branch 36 (.leaf 2021109142) (.leaf 1972510848)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1925374548) (.leaf 1879643105)) (.branch 40 (.leaf 1835262142) (.leaf 1792179895))) (.branch 43 (.branch 42 (.leaf 1750347059) (.leaf 1709716659)) (.branch 44 (.leaf 1670243919) (.leaf 1631886143))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1594602606) (.branch 47 (.leaf 1558354442) (.leaf 1523104549))) (.branch 50 (.branch 49 (.leaf 1488817495) (.leaf 1455459430)) (.branch 51 (.leaf 1422998003) (.leaf 1391402284)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1360642690) (.leaf 1330690919)) (.branch 55 (.leaf 1301519881) (.leaf 1273103637))) (.branch 58 (.branch 57 (.leaf 1245417344) (.leaf 1218437198)) (.branch 59 (.leaf 1192140382) (.leaf 1166505018))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1141510121) (.branch 62 (.leaf 1117135555) (.leaf 1093361992))) (.branch 65 (.branch 64 (.leaf 1070170874) (.leaf 1047544374)) (.branch 66 (.leaf 1025465363) (.leaf 1003917377)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 982884584) (.leaf 962351757)) (.branch 70 (.leaf 942304245) (.leaf 922727944))) (.branch 73 (.branch 72 (.leaf 903609276) (.leaf 884935164)) (.branch 74 (.leaf 866693006) (.leaf 848870658))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 831456412) (.branch 77 (.leaf 814438976) (.leaf 797807455))) (.branch 80 (.branch 79 (.leaf 781551339) (.leaf 765660478)) (.branch 81 (.leaf 750125072) (.leaf 734935657)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 720083085) (.leaf 705558516)) (.branch 85 (.leaf 691353404) (.leaf 677459484))) (.branch 88 (.branch 87 (.leaf 663868759) (.leaf 650573491)) (.branch 89 (.leaf 637566191) (.leaf 624839608)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 612386719) (.branch 92 (.leaf 600200719) (.leaf 588275016))) (.branch 95 (.branch 94 (.leaf 576603220) (.leaf 565179135)) (.branch 96 (.leaf 553996752) (.leaf 543050243)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 532333953) (.leaf 521842391)) (.branch 100 (.leaf 511570232) (.leaf 501512299))) (.branch 103 (.branch 102 (.leaf 491663570) (.leaf 482019161)) (.branch 104 (.leaf 472574330) (.leaf 463324467))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 454265090) (.leaf 445391841)) (.branch 108 (.leaf 436700483) (.leaf 428186894))) (.branch 111 (.branch 110 (.leaf 419847062) (.leaf 411677085)) (.branch 112 (.leaf 403673163) (.leaf 395831599)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388148790) (.leaf 380621231)) (.branch 116 (.leaf 373245504) (.leaf 366018282))) (.branch 119 (.branch 118 (.leaf 358936322) (.leaf 351996463)) (.branch 120 (.leaf 345195625) (.leaf 338530804)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 622).prefactor = (4926917449412447/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 622).cutoff/(generalMeanRows 622).c)).2 =
    (400003818084247/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 622).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 622).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 622).q*(generalMeanRows 622).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 622).q*(generalMeanRows 622).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 622).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 622

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 622).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 622).criticalRate j.val*(generalMeanRows 622).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 622).c*(generalMeanRows 622).criticalPoint j.val)).2-
      (generalMeanRows 622).J/2-(generalMeanRows 622).error (generalMeanGrid j.val)+
      (generalMeanRows 622).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 622).c)).2-
      (generalMeanRows 622).J/2-(generalMeanRows 622).error 4 := by
  have he : (generalMeanRows 622).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 622) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 622)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0622

/-! Kernel-checked entropy margins for general spectral rectangle 623. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0623
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5576065722) (.branch 2 (.leaf 5395187916) (.leaf 5222325658))) (.branch 5 (.branch 4 (.leaf 5057018945) (.leaf 4898840417)) (.branch 6 (.leaf 4747392514) (.leaf 4602304929)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4463232330) (.leaf 4329852317)) (.branch 10 (.leaf 4201863580) (.leaf 4078984242))) (.branch 13 (.branch 12 (.leaf 3960950353) (.leaf 3847514532)) (.branch 14 (.leaf 3738444723) (.leaf 3633523077))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3532544915) (.branch 17 (.leaf 3435317795) (.leaf 3341660650))) (.branch 20 (.branch 19 (.leaf 3251402996) (.leaf 3164384215)) (.branch 21 (.leaf 3080452881) (.leaf 2999466152)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2921289200) (.leaf 2845794693)) (.branch 25 (.leaf 2772862306) (.leaf 2702378282))) (.branch 28 (.branch 27 (.leaf 2634235008) (.leaf 2568330639)) (.branch 29 (.leaf 2504568737) (.leaf 2442857942)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2383111658) (.branch 32 (.leaf 2325247775) (.leaf 2269188394))) (.branch 35 (.branch 34 (.leaf 2214859580) (.leaf 2162191130)) (.branch 36 (.leaf 2111116357) (.leaf 2061571884)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2013497454) (.leaf 1966835757)) (.branch 40 (.leaf 1921532258) (.leaf 1877535046))) (.branch 43 (.branch 42 (.leaf 1834794685) (.leaf 1793264078)) (.branch 44 (.leaf 1752898339) (.leaf 1713654672))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1675492258) (.branch 47 (.leaf 1638372149) (.leaf 1602257167))) (.branch 50 (.branch 49 (.leaf 1567111811) (.leaf 1532902168)) (.branch 51 (.leaf 1499595829) (.leaf 1467161814)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1435570492) (.leaf 1404793519)) (.branch 55 (.leaf 1374803764) (.leaf 1345575256))) (.branch 58 (.branch 57 (.leaf 1317083118) (.leaf 1289303516)) (.branch 59 (.leaf 1262213607) (.leaf 1235791489))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1210016153) (.branch 62 (.leaf 1184867444) (.leaf 1160326013))) (.branch 65 (.branch 64 (.leaf 1136373285) (.leaf 1112991416)) (.branch 66 (.leaf 1090163261) (.leaf 1067872340)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1046102807) (.leaf 1024839422)) (.branch 70 (.leaf 1004067519) (.leaf 983772981))) (.branch 73 (.branch 72 (.leaf 963942217) (.leaf 944562136)) (.branch 74 (.leaf 925620124) (.leaf 907104022))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 889002110) (.branch 77 (.leaf 871303082) (.leaf 853996029))) (.branch 80 (.branch 79 (.leaf 837070426) (.leaf 820516108)) (.branch 81 (.leaf 804323261) (.leaf 788482403)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 772984373) (.leaf 757820313)) (.branch 85 (.leaf 742981659) (.leaf 728460128))) (.branch 88 (.branch 87 (.leaf 714247705) (.leaf 700336634)) (.branch 89 (.leaf 686719406) (.leaf 673388749)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 660337618) (.branch 92 (.leaf 647559190) (.leaf 635046848))) (.branch 95 (.branch 94 (.leaf 622794181) (.leaf 610794968)) (.branch 96 (.leaf 599043177) (.leaf 587532956)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 576258623) (.leaf 565214664)) (.branch 100 (.leaf 554395725) (.leaf 543796604))) (.branch 103 (.branch 102 (.leaf 533412250) (.leaf 523237752)) (.branch 104 (.leaf 513268340) (.leaf 503499373))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 493926340) (.leaf 484544855)) (.branch 108 (.leaf 475350648) (.leaf 466339566))) (.branch 111 (.branch 110 (.leaf 457507568) (.leaf 448850717)) (.branch 112 (.leaf 440365183) (.leaf 432047234)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 423893236) (.leaf 415899650)) (.branch 116 (.leaf 408063023) (.leaf 400379995))) (.branch 119 (.branch 118 (.leaf 392847288) (.leaf 385461706)) (.branch 120 (.leaf 378220134) (.leaf 371119533)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 623).prefactor = (4961076807755029/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 623).cutoff/(generalMeanRows 623).c)).2 =
    (81551158977713/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 623).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 623).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 623).q*(generalMeanRows 623).c/2-2 = (1169/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable162.value]
    have hcontinuation : (generalMeanRows 623).q*(generalMeanRows 623).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 623).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 623

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 623).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 623).criticalRate j.val*(generalMeanRows 623).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 623).c*(generalMeanRows 623).criticalPoint j.val)).2-
      (generalMeanRows 623).J/2-(generalMeanRows 623).error (generalMeanGrid j.val)+
      (generalMeanRows 623).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 623).c)).2-
      (generalMeanRows 623).J/2-(generalMeanRows 623).error 4 := by
  have he : (generalMeanRows 623).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 623) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 623)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0623

/-! Kernel-checked entropy margins for general spectral rectangle 624. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0624
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5258158704) (.branch 2 (.leaf 5077549298) (.leaf 4905029393))) (.branch 5 (.branch 4 (.leaf 4740138454) (.leaf 4582448423)) (.branch 6 (.leaf 4431560886) (.leaf 4287104544)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4148732952) (.leaf 4016122487)) (.branch 10 (.leaf 3888970524) (.leaf 3766993783))) (.branch 13 (.branch 12 (.leaf 3649926840) (.leaf 3537520775)) (.branch 14 (.leaf 3429541944) (.leaf 3325770859))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3226001169) (.branch 17 (.leaf 3130038729) (.leaf 3037700744))) (.branch 20 (.branch 19 (.leaf 2948814986) (.leaf 2863219079)) (.branch 21 (.leaf 2780759836) (.leaf 2701292647)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2624680923) (.leaf 2550795572)) (.branch 25 (.leaf 2479514522) (.leaf 2410722277))) (.branch 28 (.branch 27 (.leaf 2344309506) (.leaf 2280172659)) (.branch 29 (.leaf 2218213615) (.leaf 2158339350)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2100461633) (.branch 32 (.leaf 2044496741) (.leaf 1990365187))) (.branch 35 (.branch 34 (.leaf 1937991481) (.leaf 1887303891)) (.branch 36 (.leaf 1838234229) (.leaf 1790717651)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1744692463) (.leaf 1700099950)) (.branch 40 (.leaf 1656884204) (.leaf 1614991973))) (.branch 43 (.branch 42 (.leaf 1574372514) (.leaf 1534977454)) (.branch 44 (.leaf 1496760665) (.leaf 1459678143))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1423687892) (.branch 47 (.leaf 1388749819) (.leaf 1354825636))) (.branch 50 (.branch 49 (.leaf 1321878761) (.leaf 1289874235)) (.branch 51 (.leaf 1258778634) (.leaf 1228559990)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1199187721) (.leaf 1170632558)) (.branch 55 (.leaf 1142866478) (.leaf 1115862643))) (.branch 58 (.branch 57 (.leaf 1089595344) (.leaf 1064039939)) (.branch 59 (.leaf 1039172807) (.leaf 1014971294))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 991413668) (.branch 62 (.leaf 968479075) (.leaf 946147496))) (.branch 65 (.branch 64 (.leaf 924399707) (.leaf 903217243)) (.branch 66 (.leaf 882582362) (.leaf 862478010)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 842887791) (.leaf 823795934)) (.branch 70 (.leaf 805187269) (.leaf 787047194))) (.branch 73 (.branch 72 (.leaf 769361654) (.leaf 752117114)) (.branch 74 (.leaf 735300537) (.leaf 718899361))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 702901478) (.branch 77 (.leaf 687295216) (.leaf 672069319))) (.branch 80 (.branch 79 (.leaf 657212926) (.leaf 642715559)) (.branch 81 (.leaf 628567106) (.leaf 614757802)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 601278217) (.leaf 588119242)) (.branch 85 (.leaf 575272074) (.leaf 562728207))) (.branch 88 (.branch 87 (.leaf 550479415) (.leaf 538517745)) (.branch 89 (.leaf 526835504) (.leaf 515425249)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 504279774) (.branch 92 (.leaf 493392108) (.leaf 482755498))) (.branch 95 (.branch 94 (.leaf 472363406) (.leaf 462209496)) (.branch 96 (.leaf 452287631) (.leaf 442591862)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 433116423) (.leaf 423855722)) (.branch 100 (.leaf 414804338) (.leaf 405957009))) (.branch 103 (.branch 102 (.leaf 397308632) (.leaf 388854254)) (.branch 104 (.leaf 380589068) (.leaf 372508407))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364607739) (.leaf 356882661)) (.branch 108 (.leaf 349328898) (.leaf 341942295))) (.branch 111 (.branch 110 (.leaf 334718814) (.leaf 327654531)) (.branch 112 (.leaf 320745632) (.leaf 313988407)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 307379248) (.leaf 300914647)) (.branch 116 (.leaf 294591190) (.leaf 288405557))) (.branch 119 (.branch 118 (.leaf 282354516) (.leaf 276434921)) (.branch 120 (.leaf 270643709) (.leaf 264977901)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 624).prefactor = (4970552786148247/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 624).cutoff/(generalMeanRows 624).c)).2 =
    (92834587270203/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 624).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 624).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 624).q*(generalMeanRows 624).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 624).q*(generalMeanRows 624).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 624).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 624

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 624).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 624).criticalRate j.val*(generalMeanRows 624).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 624).c*(generalMeanRows 624).criticalPoint j.val)).2-
      (generalMeanRows 624).J/2-(generalMeanRows 624).error (generalMeanGrid j.val)+
      (generalMeanRows 624).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 624).c)).2-
      (generalMeanRows 624).J/2-(generalMeanRows 624).error 4 := by
  have he : (generalMeanRows 624).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 624) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 624)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0624

/-! Kernel-checked entropy margins for general spectral rectangle 625. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0625
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5384188521) (.branch 2 (.leaf 5201807420) (.leaf 5027564004))) (.branch 5 (.branch 4 (.leaf 4860994693) (.leaf 4701668625)) (.branch 6 (.leaf 4549184806) (.leaf 4403169561)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4263274252) (.leaf 4129173236)) (.branch 10 (.leaf 4000562019) (.leaf 3877155596))) (.branch 13 (.branch 12 (.leaf 3758686950) (.leaf 3644905687)) (.branch 14 (.leaf 3535576797) (.leaf 3430479530))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3329406367) (.branch 17 (.leaf 3232162079) (.leaf 3138562868))) (.branch 20 (.branch 19 (.leaf 3048435579) (.leaf 2961616973)) (.branch 21 (.leaf 2877953063) (.leaf 2797298501)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2719516009) (.leaf 2644475859)) (.branch 25 (.leaf 2572055389) (.leaf 2502138553))) (.branch 28 (.branch 27 (.leaf 2434615510) (.leaf 2369382239)) (.branch 29 (.leaf 2306340180) (.leaf 2245395902)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2186460795) (.branch 32 (.leaf 2129450783) (.leaf 2074286055))) (.branch 35 (.branch 34 (.leaf 2020890816) (.leaf 1969193051)) (.branch 36 (.leaf 1919124310) (.leaf 1870619504)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1823616714) (.leaf 1778057009)) (.branch 40 (.leaf 1733884286) (.leaf 1691045109))) (.branch 43 (.branch 42 (.leaf 1649488561) (.leaf 1609166110)) (.branch 44 (.leaf 1570031478) (.leaf 1532040520))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1495151108) (.branch 47 (.leaf 1459323026) (.leaf 1424517870))) (.branch 50 (.branch 49 (.leaf 1390698950) (.leaf 1357831202)) (.branch 51 (.leaf 1325881106) (.leaf 1294816604)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1264607026) (.leaf 1235223020)) (.branch 55 (.leaf 1206636486) (.leaf 1178820512))) (.branch 58 (.branch 57 (.leaf 1151749316) (.leaf 1125398189)) (.branch 59 (.leaf 1099743445) (.leaf 1074762366))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050433161) (.branch 62 (.leaf 1026734915) (.leaf 1003647554))) (.branch 65 (.branch 64 (.leaf 981151798) (.leaf 959229130)) (.branch 66 (.leaf 937861753) (.leaf 917032563)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 896725114) (.leaf 876923585)) (.branch 70 (.leaf 857612756) (.leaf 838777979))) (.branch 73 (.branch 72 (.leaf 820405150) (.leaf 802480688)) (.branch 74 (.leaf 784991508) (.leaf 767925001))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 751269015) (.branch 77 (.leaf 735011830) (.leaf 719142144))) (.branch 80 (.branch 79 (.leaf 703649052) (.leaf 688522029)) (.branch 81 (.leaf 673750916) (.leaf 659325904)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 645237515) (.leaf 631476595)) (.branch 85 (.leaf 618034296) (.leaf 604902064))) (.branch 88 (.branch 87 (.leaf 592071627) (.leaf 579534986)) (.branch 89 (.leaf 567284400) (.leaf 555312379)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543611672) (.branch 92 (.leaf 532175257) (.leaf 520996337))) (.branch 95 (.branch 94 (.leaf 510068323) (.leaf 499384834)) (.branch 96 (.leaf 488939683) (.leaf 478726874)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 468740590) (.leaf 458975194)) (.branch 100 (.leaf 449425212) (.leaf 440085336))) (.branch 103 (.branch 102 (.leaf 430950414) (.leaf 422015442)) (.branch 104 (.leaf 413275565) (.leaf 404726064))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396362360) (.leaf 388179999)) (.branch 108 (.leaf 380174656) (.leaf 372342127))) (.branch 111 (.branch 110 (.leaf 364678324) (.leaf 357179272)) (.branch 112 (.leaf 349841107) (.leaf 342660069)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335632501) (.leaf 328754843)) (.branch 116 (.leaf 322023633) (.leaf 315435499))) (.branch 119 (.branch 118 (.leaf 308987159) (.leaf 302675417)) (.branch 120 (.leaf 296497163) (.leaf 290449364)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 625).prefactor = (625698499909723/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 625).cutoff/(generalMeanRows 625).c)).2 =
    (378914142889271/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 625).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 625).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 625).q*(generalMeanRows 625).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 625).q*(generalMeanRows 625).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 625).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 625

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 625).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 625).criticalRate j.val*(generalMeanRows 625).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 625).c*(generalMeanRows 625).criticalPoint j.val)).2-
      (generalMeanRows 625).J/2-(generalMeanRows 625).error (generalMeanGrid j.val)+
      (generalMeanRows 625).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 625).c)).2-
      (generalMeanRows 625).J/2-(generalMeanRows 625).error 4 := by
  have he : (generalMeanRows 625).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 625) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 625)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0625

/-! Kernel-checked entropy margins for general spectral rectangle 626. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0626
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5504305011) (.branch 2 (.leaf 5315650561) (.leaf 5135438113))) (.branch 5 (.branch 4 (.leaf 4963187707) (.leaf 4798453191)) (.branch 6 (.leaf 4640819274) (.leaf 4489898890)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4345330845) (.leaf 4206777708)) (.branch 10 (.leaf 4073923905) (.leaf 3946474005))) (.branch 13 (.branch 12 (.leaf 3824151169) (.leaf 3706695741)) (.branch 14 (.leaf 3593863976) (.leaf 3485426870))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3381169103) (.branch 17 (.leaf 3280888067) (.leaf 3184392980))) (.branch 20 (.branch 19 (.leaf 3091504071) (.leaf 3002051832)) (.branch 21 (.leaf 2915876331) (.leaf 2832826578)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2752759939) (.leaf 2675541602)) (.branch 25 (.leaf 2601044069) (.leaf 2529146704))) (.branch 28 (.branch 27 (.leaf 2459735295) (.leaf 2392701664)) (.branch 29 (.leaf 2327943296) (.leaf 2265362994)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2204868561) (.branch 32 (.leaf 2146372503) (.leaf 2089791755))) (.branch 35 (.branch 34 (.leaf 2035047416) (.leaf 1982064512)) (.branch 36 (.leaf 1930771772) (.leaf 1881101411)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1832988943) (.leaf 1786372984)) (.branch 40 (.leaf 1741195089) (.leaf 1697399588))) (.branch 43 (.branch 42 (.leaf 1654933429) (.leaf 1613746041)) (.branch 44 (.leaf 1573789198) (.leaf 1535016893))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1497385220) (.branch 47 (.leaf 1460852262) (.leaf 1425377989))) (.branch 50 (.branch 49 (.leaf 1390924158) (.leaf 1357454219)) (.branch 51 (.leaf 1324933229) (.leaf 1293327772)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1262605878) (.leaf 1232736949)) (.branch 55 (.leaf 1203691695) (.leaf 1175442065))) (.branch 58 (.branch 57 (.leaf 1147961186) (.leaf 1121223307)) (.branch 59 (.leaf 1095203740) (.leaf 1069878814))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1045225819) (.branch 62 (.leaf 1021222966) (.leaf 997849340))) (.branch 65 (.branch 64 (.leaf 975084858) (.leaf 952910231)) (.branch 66 (.leaf 931306927) (.leaf 910257134)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 889743728) (.leaf 869750243)) (.branch 70 (.leaf 850260836) (.leaf 831260264))) (.branch 73 (.branch 72 (.leaf 812733854) (.leaf 794667476)) (.branch 74 (.leaf 777047524) (.leaf 759860887))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 743094932) (.branch 77 (.leaf 726737478) (.leaf 710776781))) (.branch 80 (.branch 79 (.leaf 695201513) (.leaf 680000745)) (.branch 81 (.leaf 665163928) (.leaf 650680880)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 636541766) (.leaf 622737091)) (.branch 85 (.leaf 609257676) (.leaf 596094655))) (.branch 88 (.branch 87 (.leaf 583239454) (.leaf 570683784)) (.branch 89 (.leaf 558419627) (.leaf 546439228)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534735081) (.branch 92 (.leaf 523299921) (.leaf 512126715))) (.branch 95 (.branch 94 (.leaf 501208652) (.leaf 490539134)) (.branch 96 (.leaf 480111769) (.leaf 469920364)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 459958913) (.leaf 450221595)) (.branch 100 (.leaf 440702765) (.leaf 431396948))) (.branch 103 (.branch 102 (.leaf 422298830) (.leaf 413403257)) (.branch 104 (.leaf 404705225) (.leaf 396199877))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 387882497) (.leaf 379748504)) (.branch 108 (.leaf 371793449) (.leaf 364013009))) (.branch 111 (.branch 110 (.leaf 356402982) (.leaf 348959287)) (.branch 112 (.leaf 341677955) (.leaf 334555126)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 327587047) (.leaf 320770070)) (.branch 116 (.leaf 314100642) (.leaf 307575310))) (.branch 119 (.branch 118 (.leaf 301190711) (.leaf 294943575)) (.branch 120 (.leaf 288830714) (.leaf 282849030)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 626).prefactor = (1289005599555631/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 626).cutoff/(generalMeanRows 626).c)).2 =
    (370332565742317/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 626).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 626).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 626).q*(generalMeanRows 626).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 626).q*(generalMeanRows 626).cutoff/2-2 = (8210/3979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable211.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 626).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 626

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 626).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 626).criticalRate j.val*(generalMeanRows 626).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 626).c*(generalMeanRows 626).criticalPoint j.val)).2-
      (generalMeanRows 626).J/2-(generalMeanRows 626).error (generalMeanGrid j.val)+
      (generalMeanRows 626).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 626).c)).2-
      (generalMeanRows 626).J/2-(generalMeanRows 626).error 4 := by
  have he : (generalMeanRows 626).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 626) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 626)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0626

/-! Kernel-checked entropy margins for general spectral rectangle 627. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0627
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5733018265) (.branch 2 (.leaf 5542024122) (.leaf 5359514007))) (.branch 5 (.branch 4 (.leaf 5185004846) (.leaf 5018047654)) (.branch 6 (.leaf 4858224561) (.leaf 4705146155)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4558449106) (.leaf 4417794040)) (.branch 10 (.leaf 4282863613) (.leaf 4153360787))) (.branch 13 (.branch 12 (.leaf 4029007261) (.leaf 3909542055)) (.branch 14 (.leaf 3794720218) (.leaf 3684311654))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3578100056) (.branch 17 (.leaf 3475881924) (.leaf 3377465668))) (.branch 20 (.branch 19 (.leaf 3282670791) (.leaf 3191327132)) (.branch 21 (.leaf 3103274171) (.leaf 3018360395)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2936442702) (.leaf 2857385862)) (.branch 25 (.leaf 2781062008) (.leaf 2707350176))) (.branch 28 (.branch 27 (.leaf 2636135871) (.leaf 2567310663)) (.branch 29 (.leaf 2500771819) (.leaf 2436421956)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2374168718) (.branch 32 (.leaf 2313924476) (.leaf 2255606053))) (.branch 35 (.branch 34 (.leaf 2199134456) (.leaf 2144434640)) (.branch 36 (.leaf 2091435276) (.leaf 2040068541)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1990269919) (.leaf 1941978013)) (.branch 40 (.leaf 1895134374) (.leaf 1849683334))) (.branch 43 (.branch 42 (.leaf 1805571859) (.leaf 1762749396)) (.branch 44 (.leaf 1721167748) (.leaf 1680780941))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1641545106) (.branch 47 (.leaf 1603418369) (.leaf 1566360745))) (.branch 50 (.branch 49 (.leaf 1530334038) (.leaf 1495301749)) (.branch 51 (.leaf 1461228987) (.leaf 1428082386)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1395830031) (.leaf 1364441376)) (.branch 55 (.leaf 1333887186) (.leaf 1304139462))) (.branch 58 (.branch 57 (.leaf 1275171382) (.leaf 1246957246)) (.branch 59 (.leaf 1219472416) (.leaf 1192693268))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1166597139) (.branch 62 (.leaf 1141162284) (.leaf 1116367830))) (.branch 65 (.branch 64 (.leaf 1092193734) (.leaf 1068620745)) (.branch 66 (.leaf 1045630364) (.leaf 1023204815)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1001327001) (.leaf 979980484)) (.branch 70 (.leaf 959149447) (.leaf 938818666))) (.branch 73 (.branch 72 (.leaf 918973488) (.leaf 899599801)) (.branch 74 (.leaf 880684010) (.leaf 862213015))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 844174190) (.branch 77 (.leaf 826555361) (.leaf 809344783))) (.branch 80 (.branch 79 (.leaf 792531129) (.leaf 776103466)) (.branch 81 (.leaf 760051238) (.leaf 744364253)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 729032667) (.leaf 714046967)) (.branch 85 (.leaf 699397960) (.leaf 685076758))) (.branch 88 (.branch 87 (.leaf 671074767) (.leaf 657383672)) (.branch 89 (.leaf 643995429) (.leaf 630902252)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 618096606) (.branch 92 (.leaf 605571190) (.leaf 593318936))) (.branch 95 (.branch 94 (.leaf 581332995) (.leaf 569606729)) (.branch 96 (.leaf 558133703) (.leaf 546907679)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 535922607) (.leaf 525172618)) (.branch 100 (.leaf 514652017) (.leaf 504355277))) (.branch 103 (.branch 102 (.leaf 494277033) (.leaf 484412074)) (.branch 104 (.leaf 474755342) (.leaf 465301923))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 456047039) (.leaf 446986052)) (.branch 108 (.leaf 438114449) (.leaf 429427846))) (.branch 111 (.branch 110 (.leaf 420921977) (.leaf 412592696)) (.branch 112 (.leaf 404435966) (.leaf 396447861)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388624561) (.leaf 380962347)) (.branch 116 (.leaf 373457598) (.leaf 366106788))) (.branch 119 (.branch 118 (.leaf 358906485) (.leaf 351853343)) (.branch 120 (.leaf 344944105) (.leaf 338175597)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 627).prefactor = (1298254858981459/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 627).cutoff/(generalMeanRows 627).c)).2 =
    (96444222042447/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 627).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 627).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 627).q*(generalMeanRows 627).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    have hcontinuation : (generalMeanRows 627).q*(generalMeanRows 627).cutoff/2-2 = (8210/3979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable211.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 627).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 627

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 627).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 627).criticalRate j.val*(generalMeanRows 627).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 627).c*(generalMeanRows 627).criticalPoint j.val)).2-
      (generalMeanRows 627).J/2-(generalMeanRows 627).error (generalMeanGrid j.val)+
      (generalMeanRows 627).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 627).c)).2-
      (generalMeanRows 627).J/2-(generalMeanRows 627).error 4 := by
  have he : (generalMeanRows 627).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 627) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 627)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0627

/-! Kernel-checked entropy margins for general spectral rectangle 628. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0628
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5607377582) (.branch 2 (.leaf 5422814868) (.leaf 5246427828))) (.branch 5 (.branch 4 (.leaf 5077749930) (.leaf 4916347630)) (.branch 6 (.leaf 4761817499) (.leaf 4613783645)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4471895419) (.leaf 4335825350)) (.branch 10 (.leaf 4205267283) (.leaf 4079934710))) (.branch 13 (.branch 12 (.leaf 3959559246) (.leaf 3843889261)) (.branch 14 (.leaf 3732688628) (.leaf 3625735586))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3522821704) (.branch 17 (.leaf 3423750933) (.leaf 3328338737))) (.branch 20 (.branch 19 (.leaf 3236411299) (.leaf 3147804789)) (.branch 21 (.leaf 3062364694) (.leaf 2979945195)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2900408601) (.leaf 2823624818)) (.branch 25 (.leaf 2749470862) (.leaf 2677830411))) (.branch 28 (.branch 27 (.leaf 2608593381) (.leaf 2541655543)) (.branch 29 (.leaf 2476918162) (.leaf 2414287660)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2353675307) (.branch 32 (.leaf 2294996927) (.leaf 2238172635))) (.branch 35 (.branch 34 (.leaf 2183126578) (.leaf 2129786701)) (.branch 36 (.leaf 2078084533) (.leaf 2027954973)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1979336104) (.leaf 1932169012)) (.branch 40 (.leaf 1886397617) (.leaf 1841968515))) (.branch 43 (.branch 42 (.leaf 1798830831) (.leaf 1756936080)) (.branch 44 (.leaf 1716238036) (.leaf 1676692612))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1638257743) (.branch 47 (.leaf 1600893278) (.leaf 1564560881))) (.branch 50 (.branch 49 (.leaf 1529223932) (.leaf 1494847440)) (.branch 51 (.leaf 1461397957) (.leaf 1428843499)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1397153470) (.leaf 1366298591)) (.branch 55 (.leaf 1336250836) (.leaf 1306983363))) (.branch 58 (.branch 57 (.leaf 1278470463) (.leaf 1250687497)) (.branch 59 (.leaf 1223610844) (.leaf 1197217854))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1171486800) (.branch 62 (.leaf 1146396829) (.leaf 1121927924))) (.branch 65 (.branch 64 (.leaf 1098060865) (.leaf 1074777187)) (.branch 66 (.leaf 1052059146) (.leaf 1029889686)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1008252405) (.leaf 987131528)) (.branch 70 (.leaf 966511874) (.leaf 946378832))) (.branch 73 (.branch 72 (.leaf 926718331) (.leaf 907516821)) (.branch 74 (.leaf 888761245) (.leaf 870439021))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 852538015) (.branch 77 (.leaf 835046529) (.leaf 817953275))) (.branch 80 (.branch 79 (.leaf 801247360) (.leaf 784918271)) (.branch 81 (.leaf 768955855) (.leaf 753350305)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 738092148) (.leaf 723172224)) (.branch 85 (.leaf 708581683) (.leaf 694311963))) (.branch 88 (.branch 87 (.leaf 680354784) (.leaf 666702131)) (.branch 89 (.leaf 653346251) (.leaf 640279635)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 627495012) (.branch 92 (.leaf 614985339) (.leaf 602743792))) (.branch 95 (.branch 94 (.leaf 590763758) (.leaf 579038824)) (.branch 96 (.leaf 567562773) (.leaf 556329576)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 545333381) (.leaf 534568511)) (.branch 100 (.leaf 524029455) (.leaf 513710864))) (.branch 103 (.branch 102 (.leaf 503607541) (.leaf 493714440)) (.branch 104 (.leaf 484026658) (.leaf 474539430))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 465248124) (.leaf 456148239)) (.branch 108 (.leaf 447235395) (.leaf 438505335))) (.branch 111 (.branch 110 (.leaf 429953916) (.leaf 421577108)) (.branch 112 (.leaf 413370988) (.leaf 405331737)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 397455639) (.leaf 389739073)) (.branch 116 (.leaf 382178516) (.leaf 374770531))) (.branch 119 (.branch 118 (.leaf 367511775) (.leaf 360398987)) (.branch 120 (.leaf 353428989) (.leaf 346598685)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 628).prefactor = (5040870160022971/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 628).cutoff/(generalMeanRows 628).c)).2 =
    (49280014170937/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 628).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 628).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 628).q*(generalMeanRows 628).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 628).q*(generalMeanRows 628).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 628).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 628

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 628).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 628).criticalRate j.val*(generalMeanRows 628).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 628).c*(generalMeanRows 628).criticalPoint j.val)).2-
      (generalMeanRows 628).J/2-(generalMeanRows 628).error (generalMeanGrid j.val)+
      (generalMeanRows 628).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 628).c)).2-
      (generalMeanRows 628).J/2-(generalMeanRows 628).error 4 := by
  have he : (generalMeanRows 628).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 628) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 628)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0628

/-! Kernel-checked entropy margins for general spectral rectangle 629. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0629
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5841903700) (.branch 2 (.leaf 5655295613) (.leaf 5476899404))) (.branch 5 (.branch 4 (.leaf 5306245448) (.leaf 5142897390)) (.branch 6 (.leaf 4986449242) (.leaf 4836522789)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4692765267) (.leaf 4554847283)) (.branch 10 (.leaf 4422460940) (.leaf 4295318145))) (.branch 13 (.branch 12 (.leaf 4173149080) (.leaf 4055700815)) (.branch 14 (.leaf 3942736047) (.leaf 3834031956))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3729379153) (.branch 17 (.leaf 3628580730) (.leaf 3531451380))) (.branch 20 (.branch 19 (.leaf 3437816595) (.leaf 3347511930)) (.branch 21 (.leaf 3260382323) (.leaf 3176281473)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3095071261) (.leaf 3016621219)) (.branch 25 (.leaf 2940808040) (.leaf 2867515119))) (.branch 28 (.branch 27 (.leaf 2796632135) (.leaf 2728054656)) (.branch 29 (.leaf 2661683779) (.leaf 2597425789)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2535191847) (.branch 32 (.leaf 2474897697) (.leaf 2416463393))) (.branch 35 (.branch 34 (.leaf 2359813045) (.leaf 2304874581)) (.branch 36 (.leaf 2251579529) (.leaf 2199862803)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2149662517) (.leaf 2100919798)) (.branch 40 (.leaf 2053578619) (.leaf 2007585641))) (.branch 43 (.branch 42 (.leaf 1962890061) (.leaf 1919443474)) (.branch 44 (.leaf 1877199741) (.leaf 1836114869))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1796146890) (.branch 47 (.leaf 1757255755) (.leaf 1719403235))) (.branch 50 (.branch 49 (.leaf 1682552817) (.leaf 1646669621)) (.branch 51 (.leaf 1611720311) (.leaf 1577673017)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1544497256) (.leaf 1512163864)) (.branch 55 (.leaf 1480644927) (.leaf 1449913719))) (.branch 58 (.branch 57 (.leaf 1419944641) (.leaf 1390713165)) (.branch 59 (.leaf 1362195781) (.leaf 1334369946))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1307214038) (.branch 62 (.leaf 1280707309) (.leaf 1254829842))) (.branch 65 (.branch 64 (.leaf 1229562516) (.leaf 1204886962)) (.branch 66 (.leaf 1180785528) (.leaf 1157241250)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1134237813) (.leaf 1111759524)) (.branch 70 (.leaf 1089791285) (.leaf 1068318561))) (.branch 73 (.branch 72 (.leaf 1047327358) (.leaf 1026804195)) (.branch 74 (.leaf 1006736083) (.leaf 987110505))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 967915388) (.branch 77 (.leaf 949139092) (.leaf 930770382))) (.branch 80 (.branch 79 (.leaf 912798418) (.leaf 895212734)) (.branch 81 (.leaf 878003221) (.leaf 861160113)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 844673975) (.leaf 828535683)) (.branch 85 (.leaf 812736417) (.leaf 797267644))) (.branch 88 (.branch 87 (.leaf 782121108) (.leaf 767288819)) (.branch 89 (.leaf 752763040) (.leaf 738536280)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 724601281) (.branch 92 (.leaf 710951011) (.leaf 697578654))) (.branch 95 (.branch 94 (.leaf 684477600) (.leaf 671641440)) (.branch 96 (.leaf 659063957) (.leaf 646739118)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 634661067) (.leaf 622824118)) (.branch 100 (.leaf 611222751) (.leaf 599851603))) (.branch 103 (.branch 102 (.leaf 588705463) (.leaf 577779269)) (.branch 104 (.leaf 567068098) (.leaf 556567164))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 546271813) (.leaf 536177517)) (.branch 108 (.leaf 526279871) (.leaf 516574588))) (.branch 111 (.branch 110 (.leaf 507057495) (.leaf 497724529)) (.branch 112 (.leaf 488571732) (.leaf 479595253)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 470791336) (.leaf 462156323)) (.branch 116 (.leaf 453686648) (.leaf 445378836))) (.branch 119 (.branch 118 (.leaf 437229500) (.leaf 429235334)) (.branch 120 (.leaf 421393116) (.leaf 413699703)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 629).prefactor = (2538200504503793/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 629).cutoff/(generalMeanRows 629).c)).2 =
    (204902314954303/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 629).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 629).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 629).q*(generalMeanRows 629).c/2-2 = (227/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable159.value]
    have hcontinuation : (generalMeanRows 629).q*(generalMeanRows 629).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 629).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 629

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 629).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 629).criticalRate j.val*(generalMeanRows 629).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 629).c*(generalMeanRows 629).criticalPoint j.val)).2-
      (generalMeanRows 629).J/2-(generalMeanRows 629).error (generalMeanGrid j.val)+
      (generalMeanRows 629).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 629).c)).2-
      (generalMeanRows 629).J/2-(generalMeanRows 629).error 4 := by
  have he : (generalMeanRows 629).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 629) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 629)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0629

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock08 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 8 i) := by
  fin_cases i
  · exact EntropyRow0560.numerical
  · exact EntropyRow0561.numerical
  · exact EntropyRow0562.numerical
  · exact EntropyRow0563.numerical
  · exact EntropyRow0564.numerical
  · exact EntropyRow0565.numerical
  · exact EntropyRow0566.numerical
  · exact EntropyRow0567.numerical
  · exact EntropyRow0568.numerical
  · exact EntropyRow0569.numerical
  · exact EntropyRow0570.numerical
  · exact EntropyRow0571.numerical
  · exact EntropyRow0572.numerical
  · exact EntropyRow0573.numerical
  · exact EntropyRow0574.numerical
  · exact EntropyRow0575.numerical
  · exact EntropyRow0576.numerical
  · exact EntropyRow0577.numerical
  · exact EntropyRow0578.numerical
  · exact EntropyRow0579.numerical
  · exact EntropyRow0580.numerical
  · exact EntropyRow0581.numerical
  · exact EntropyRow0582.numerical
  · exact EntropyRow0583.numerical
  · exact EntropyRow0584.numerical
  · exact EntropyRow0585.numerical
  · exact EntropyRow0586.numerical
  · exact EntropyRow0587.numerical
  · exact EntropyRow0588.numerical
  · exact EntropyRow0589.numerical
  · exact EntropyRow0590.numerical
  · exact EntropyRow0591.numerical
  · exact EntropyRow0592.numerical
  · exact EntropyRow0593.numerical
  · exact EntropyRow0594.numerical
  · exact EntropyRow0595.numerical
  · exact EntropyRow0596.numerical
  · exact EntropyRow0597.numerical
  · exact EntropyRow0598.numerical
  · exact EntropyRow0599.numerical
  · exact EntropyRow0600.numerical
  · exact EntropyRow0601.numerical
  · exact EntropyRow0602.numerical
  · exact EntropyRow0603.numerical
  · exact EntropyRow0604.numerical
  · exact EntropyRow0605.numerical
  · exact EntropyRow0606.numerical
  · exact EntropyRow0607.numerical
  · exact EntropyRow0608.numerical
  · exact EntropyRow0609.numerical
  · exact EntropyRow0610.numerical
  · exact EntropyRow0611.numerical
  · exact EntropyRow0612.numerical
  · exact EntropyRow0613.numerical
  · exact EntropyRow0614.numerical
  · exact EntropyRow0615.numerical
  · exact EntropyRow0616.numerical
  · exact EntropyRow0617.numerical
  · exact EntropyRow0618.numerical
  · exact EntropyRow0619.numerical
  · exact EntropyRow0620.numerical
  · exact EntropyRow0621.numerical
  · exact EntropyRow0622.numerical
  · exact EntropyRow0623.numerical
  · exact EntropyRow0624.numerical
  · exact EntropyRow0625.numerical
  · exact EntropyRow0626.numerical
  · exact EntropyRow0627.numerical
  · exact EntropyRow0628.numerical
  · exact EntropyRow0629.numerical
end SingularValueBounds.KL.Certificates
