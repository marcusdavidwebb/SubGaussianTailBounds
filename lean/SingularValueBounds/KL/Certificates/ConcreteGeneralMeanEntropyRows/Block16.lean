import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs
import SingularValueBounds.KL.Certificates.GeneralMeanPrefactorLogs
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block16
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block18
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block20
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block21
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block23
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block24
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block25
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1120. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1120
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6434077777) (.branch 2 (.leaf 6246881302) (.leaf 6067153125))) (.branch 5 (.branch 4 (.leaf 5894484210) (.leaf 5728494538)) (.branch 6 (.leaf 5568830539) (.leaf 5415162796)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5267184004) (.leaf 5124607131)) (.branch 10 (.leaf 4987163769) (.leaf 4854602647))) (.branch 13 (.branch 12 (.leaf 4726688289) (.leaf 4603199798)) (.branch 14 (.leaf 4483929752) (.leaf 4368683204))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4257276765) (.branch 17 (.leaf 4149537776) (.leaf 4045303543))) (.branch 20 (.branch 19 (.leaf 3944420638) (.leaf 3846744263)) (.branch 21 (.leaf 3752137664) (.leaf 3660471586)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3571623778) (.leaf 3485478539)) (.branch 25 (.leaf 3401926285) (.leaf 3320863169))) (.branch 28 (.branch 27 (.leaf 3242190710) (.leaf 3165815462)) (.branch 29 (.leaf 3091648704) (.leaf 3019606147)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2949607671) (.branch 32 (.leaf 2881577072) (.leaf 2815441833))) (.branch 35 (.branch 34 (.leaf 2751132905) (.leaf 2688584507)) (.branch 36 (.leaf 2627733939) (.leaf 2568521407)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2510889854) (.leaf 2454784815)) (.branch 40 (.leaf 2400154267) (.leaf 2346948498))) (.branch 43 (.branch 42 (.leaf 2295119980) (.leaf 2244623254)) (.branch 44 (.leaf 2195414814) (.leaf 2147453012))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2100697950) (.branch 47 (.leaf 2055111399) (.leaf 2010656705))) (.branch 50 (.branch 49 (.leaf 1967298714) (.leaf 1925003693)) (.branch 51 (.leaf 1883739258) (.leaf 1843474311)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1804178971) (.leaf 1765824518)) (.branch 55 (.leaf 1728383335) (.leaf 1691828855))) (.branch 58 (.branch 57 (.leaf 1656135512) (.leaf 1621278693)) (.branch 59 (.leaf 1587234691) (.leaf 1553980668))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1521494609) (.branch 62 (.leaf 1489755289) (.leaf 1458742235))) (.branch 65 (.branch 64 (.leaf 1428435690) (.leaf 1398816588)) (.branch 66 (.leaf 1369866515) (.leaf 1341567687)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1313902919) (.leaf 1286855601)) (.branch 70 (.leaf 1260409672) (.leaf 1234549599))) (.branch 73 (.branch 72 (.leaf 1209260351) (.leaf 1184527384)) (.branch 74 (.leaf 1160336615) (.leaf 1136674408))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1113527550) (.branch 77 (.leaf 1090883242) (.leaf 1068729077))) (.branch 80 (.branch 79 (.leaf 1047053024) (.leaf 1025843418)) (.branch 81 (.leaf 1005088942) (.leaf 984778614)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 964901777) (.leaf 945448083)) (.branch 85 (.leaf 926407484) (.leaf 907770222))) (.branch 88 (.branch 87 (.leaf 889526815) (.leaf 871668048)) (.branch 89 (.leaf 854184966) (.leaf 837068862)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 820311269) (.branch 92 (.leaf 803903952) (.leaf 787838901))) (.branch 95 (.branch 94 (.leaf 772108319) (.leaf 756704621)) (.branch 96 (.leaf 741620421) (.leaf 726848531)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 712381948) (.leaf 698213854)) (.branch 100 (.leaf 684337605) (.leaf 670746731))) (.branch 103 (.branch 102 (.leaf 657434925) (.leaf 644396040)) (.branch 104 (.leaf 631624084) (.leaf 619113217))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 606857742) (.leaf 594852104)) (.branch 108 (.leaf 583090886) (.leaf 571568802))) (.branch 111 (.branch 110 (.leaf 560280697) (.leaf 549221537)) (.branch 112 (.leaf 538386413) (.leaf 527770533)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 517369217) (.leaf 507177900)) (.branch 116 (.leaf 497192120) (.leaf 487407525))) (.branch 119 (.branch 118 (.leaf 477819860) (.leaf 468424973)) (.branch 120 (.leaf 459218807) (.leaf 450197396)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1120).prefactor = (5290962243330371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1120).cutoff/(generalMeanRows 1120).c)).2 =
    (420492347231433/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1120).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1120).q*(generalMeanRows 1120).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 1120).q*(generalMeanRows 1120).cutoff/2-2 = (3116/1403:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable372.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1120).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1120).criticalRate j.val*(generalMeanRows 1120).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1120).c*(generalMeanRows 1120).criticalPoint j.val)).2-
      (generalMeanRows 1120).J/2-(generalMeanRows 1120).error (generalMeanGrid j.val)+
      (generalMeanRows 1120).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1120).c)).2-
      (generalMeanRows 1120).J/2-(generalMeanRows 1120).error 4 := by
  have he : (generalMeanRows 1120).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1120) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1120)
    (generalMeanRows_prefactorDomain 1120) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1120

/-! Kernel-checked entropy margins for general spectral rectangle 1121. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1121
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6531274826) (.branch 2 (.leaf 6336308835) (.leaf 6149186166))) (.branch 5 (.branch 4 (.leaf 5969478116) (.leaf 5796786304)) (.branch 6 (.leaf 5630739994) (.leaf 5470993698)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5317225042) (.leaf 5169132849)) (.branch 10 (.leaf 5026435418) (.leaf 4888868971))) (.branch 13 (.branch 12 (.leaf 4756186251) (.leaf 4628155253)) (.branch 14 (.leaf 4504558074) (.leaf 4385189863))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4269857872) (.branch 17 (.leaf 4158380579) (.leaf 4050586902))) (.branch 20 (.branch 19 (.leaf 3946315460) (.leaf 3845413915)) (.branch 21 (.leaf 3747738353) (.leaf 3653152721)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3561528308) (.leaf 3472743265)) (.branch 25 (.leaf 3386682163) (.leaf 3303235588))) (.branch 28 (.branch 27 (.leaf 3222299755) (.leaf 3143776164)) (.branch 29 (.leaf 3067571272) (.leaf 2993596193)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2921766414) (.branch 32 (.leaf 2852001541) (.leaf 2784225049))) (.branch 35 (.branch 34 (.leaf 2718364062) (.leaf 2654349137)) (.branch 36 (.leaf 2592114072) (.leaf 2531595721)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2472733819) (.leaf 2415470828)) (.branch 40 (.leaf 2359751783) (.leaf 2305524149))) (.branch 43 (.branch 42 (.leaf 2252737697) (.leaf 2201344373)) (.branch 44 (.leaf 2151298185) (.leaf 2102555098))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2055072927) (.branch 47 (.leaf 2008811241) (.leaf 1963731278))) (.branch 50 (.branch 49 (.leaf 1919795856) (.leaf 1876969295)) (.branch 51 (.leaf 1835217341) (.leaf 1794507095)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1754806950) (.leaf 1716086522)) (.branch 55 (.leaf 1678316596) (.leaf 1641469070))) (.branch 58 (.branch 57 (.leaf 1605516897) (.leaf 1570434042)) (.branch 59 (.leaf 1536195430) (.leaf 1502776905))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1470155183) (.branch 62 (.leaf 1438307818) (.leaf 1407213162))) (.branch 65 (.branch 64 (.leaf 1376850328) (.leaf 1347199158)) (.branch 66 (.leaf 1318240189) (.leaf 1289954626)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1262324310) (.leaf 1235331693)) (.branch 70 (.leaf 1208959810) (.leaf 1183192257))) (.branch 73 (.branch 72 (.leaf 1158013165) (.leaf 1133407180)) (.branch 74 (.leaf 1109359440) (.leaf 1085855558))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1062881600) (.branch 77 (.leaf 1040424068) (.leaf 1018469881))) (.branch 80 (.branch 79 (.leaf 997006364) (.leaf 976021226)) (.branch 81 (.leaf 955502549) (.leaf 935438771)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 915818676) (.leaf 896631379)) (.branch 85 (.leaf 877866313) (.leaf 859513218))) (.branch 88 (.branch 87 (.leaf 841562132) (.leaf 824003377)) (.branch 89 (.leaf 806827549) (.leaf 790025511)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 773588382) (.branch 92 (.leaf 757507526) (.leaf 741774547))) (.branch 95 (.branch 94 (.leaf 726381280) (.leaf 711319780)) (.branch 96 (.leaf 696582320) (.leaf 682161378)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 668049636) (.leaf 654239966)) (.branch 100 (.leaf 640725432) (.leaf 627499278))) (.branch 103 (.branch 102 (.leaf 614554923) (.leaf 601885960)) (.branch 104 (.leaf 589486143) (.leaf 577349388))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 565469766) (.leaf 553841498)) (.branch 108 (.leaf 542458950) (.leaf 531316630))) (.branch 111 (.branch 110 (.leaf 520409182) (.leaf 509731384)) (.branch 112 (.leaf 499278142) (.leaf 489044488)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 479025575) (.leaf 469216673)) (.branch 116 (.leaf 459613168) (.leaf 450210558))) (.branch 119 (.branch 118 (.leaf 441004446) (.leaf 431990543)) (.branch 120 (.leaf 423164662) (.leaf 414522714)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1121).prefactor = (1105709512679277/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1121).cutoff/(generalMeanRows 1121).c)).2 =
    (163677116791/400000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1121).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1121).q*(generalMeanRows 1121).c/2-2 = (1607/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable174.value]
  have hcontinuation : (generalMeanRows 1121).q*(generalMeanRows 1121).cutoff/2-2 = (3116/1403:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable372.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1121).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1121).criticalRate j.val*(generalMeanRows 1121).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1121).c*(generalMeanRows 1121).criticalPoint j.val)).2-
      (generalMeanRows 1121).J/2-(generalMeanRows 1121).error (generalMeanGrid j.val)+
      (generalMeanRows 1121).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1121).c)).2-
      (generalMeanRows 1121).J/2-(generalMeanRows 1121).error 4 := by
  have he : (generalMeanRows 1121).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1121) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1121)
    (generalMeanRows_prefactorDomain 1121) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1121

/-! Kernel-checked entropy margins for general spectral rectangle 1122. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1122
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6352224325) (.branch 2 (.leaf 6150683629) (.leaf 5957432714))) (.branch 5 (.branch 4 (.leaf 5772019903) (.leaf 5594025239)) (.branch 6 (.leaf 5423057698) (.leaf 5258752687)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5100769821) (.leaf 4948790922)) (.branch 10 (.leaf 4802518224) (.leaf 4661672754))) (.branch 13 (.branch 12 (.leaf 4525992868) (.leaf 4395232927)) (.branch 14 (.leaf 4269162095) (.leaf 4147563245))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4030231967) (.branch 17 (.leaf 3916975655) (.leaf 3807612677))) (.branch 20 (.branch 19 (.leaf 3701971619) (.leaf 3599890578)) (.branch 21 (.leaf 3501216530) (.leaf 3405804733)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3313518190) (.leaf 3224227142)) (.branch 25 (.leaf 3137808611) (.leaf 3054145965))) (.branch 28 (.branch 27 (.leaf 2973128528) (.leaf 2894651212)) (.branch 29 (.leaf 2818614173) (.leaf 2744922499)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2673485911) (.branch 32 (.leaf 2604218497) (.leaf 2537038449))) (.branch 35 (.branch 34 (.leaf 2471867833) (.leaf 2408632363)) (.branch 36 (.leaf 2347261196) (.leaf 2287686740)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2229844472) (.leaf 2173672770)) (.branch 40 (.leaf 2119112755) (.leaf 2066108144))) (.branch 43 (.branch 42 (.leaf 2014605110) (.leaf 1964552151)) (.branch 44 (.leaf 1915899971) (.leaf 1868601364))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1822611104) (.branch 47 (.leaf 1777885847) (.leaf 1734384035))) (.branch 50 (.branch 49 (.leaf 1692065804) (.leaf 1650892904)) (.branch 51 (.leaf 1610828615) (.leaf 1571837676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1533886209) (.leaf 1496941661)) (.branch 55 (.leaf 1460972730) (.leaf 1425949317))) (.branch 58 (.branch 57 (.leaf 1391842462) (.leaf 1358624291)) (.branch 59 (.leaf 1326267973) (.leaf 1294747664))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1264038467) (.branch 62 (.leaf 1234116390) (.leaf 1204958302))) (.branch 65 (.branch 64 (.leaf 1176541898) (.leaf 1148845662)) (.branch 66 (.leaf 1121848832) (.leaf 1095531369)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1069873925) (.leaf 1044857813)) (.branch 70 (.leaf 1020464982) (.leaf 996677988))) (.branch 73 (.branch 72 (.leaf 973479969) (.leaf 950854622)) (.branch 74 (.leaf 928786181) (.leaf 907259394))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 886259503) (.branch 77 (.leaf 865772224) (.leaf 845783728))) (.branch 80 (.branch 79 (.leaf 826280626) (.leaf 807249948)) (.branch 81 (.leaf 788679131) (.leaf 770555999)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 752868753) (.leaf 735605952)) (.branch 85 (.leaf 718756506) (.leaf 702309657))) (.branch 88 (.branch 87 (.leaf 686254969) (.leaf 670582319)) (.branch 89 (.leaf 655281882) (.leaf 640344121)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 625759780) (.branch 92 (.leaf 611519869) (.leaf 597615659))) (.branch 95 (.branch 94 (.leaf 584038672) (.leaf 570780671)) (.branch 96 (.leaf 557833653) (.leaf 545189840)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 532841673) (.leaf 520781804)) (.branch 100 (.leaf 509003088) (.leaf 497498579))) (.branch 103 (.branch 102 (.leaf 486261520) (.leaf 475285339)) (.branch 104 (.leaf 464563645) (.leaf 454090216))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443859001) (.leaf 433864111)) (.branch 108 (.leaf 424099812) (.leaf 414560523))) (.branch 111 (.branch 110 (.leaf 405240814) (.leaf 396135393)) (.branch 112 (.leaf 387239111) (.leaf 378546951)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 370054027) (.leaf 361755582)) (.branch 116 (.leaf 353646978) (.leaf 345723700))) (.branch 119 (.branch 118 (.leaf 337981346) (.leaf 330415628)) (.branch 120 (.leaf 323022367) (.leaf 315797490)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1122).prefactor = (722100176562053/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1122).cutoff/(generalMeanRows 1122).c)).2 =
    (95372547357041/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1122).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1122).q*(generalMeanRows 1122).c/2-2 = (3529/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable373.value]
  have hcontinuation : (generalMeanRows 1122).q*(generalMeanRows 1122).cutoff/2-2 = (3116/1403:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable372.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1122).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1122).criticalRate j.val*(generalMeanRows 1122).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1122).c*(generalMeanRows 1122).criticalPoint j.val)).2-
      (generalMeanRows 1122).J/2-(generalMeanRows 1122).error (generalMeanGrid j.val)+
      (generalMeanRows 1122).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1122).c)).2-
      (generalMeanRows 1122).J/2-(generalMeanRows 1122).error 4 := by
  have he : (generalMeanRows 1122).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1122) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1122)
    (generalMeanRows_prefactorDomain 1122) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1122

/-! Kernel-checked entropy margins for general spectral rectangle 1123. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1123
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6297975161) (.branch 2 (.leaf 6110457701) (.leaf 5930512267))) (.branch 5 (.branch 4 (.leaf 5757719962) (.leaf 5591691848)) (.branch 6 (.leaf 5432066286) (.leaf 5278506571)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5130698809) (.leaf 4988350016)) (.branch 10 (.leaf 4851186409) (.leaf 4718951866))) (.branch 13 (.branch 12 (.leaf 4591406531) (.leaf 4468325558)) (.branch 14 (.leaf 4349497966) (.leaf 4234725595))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4123822169) (.branch 17 (.leaf 4016612422) (.leaf 3912931314))) (.branch 20 (.branch 19 (.leaf 3812623310) (.leaf 3715541714)) (.branch 21 (.leaf 3621548061) (.leaf 3530511562)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3442308587) (.leaf 3356822189)) (.branch 25 (.leaf 3273941670) (.leaf 3193562176))) (.branch 28 (.branch 27 (.leaf 3115584322) (.leaf 3039913847)) (.branch 29 (.leaf 2966461295) (.leaf 2895141716)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2825874389) (.branch 32 (.leaf 2758582568) (.leaf 2693193244))) (.branch 35 (.branch 34 (.leaf 2629636921) (.leaf 2567847410)) (.branch 36 (.leaf 2507761639) (.leaf 2449319469)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2392463530) (.leaf 2337139063)) (.branch 40 (.leaf 2283293775) (.leaf 2230877699))) (.branch 43 (.branch 42 (.leaf 2179843070) (.leaf 2130144202)) (.branch 44 (.leaf 2081737378) (.leaf 2034580743))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1988634206) (.branch 47 (.leaf 1943859348) (.leaf 1900219333))) (.branch 50 (.branch 49 (.leaf 1857678830) (.leaf 1816203932)) (.branch 51 (.leaf 1775762086) (.leaf 1736322024)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1697853702) (.leaf 1660328236)) (.branch 55 (.leaf 1623717847) (.leaf 1587995808))) (.branch 58 (.branch 57 (.leaf 1553136392) (.leaf 1519114828)) (.branch 59 (.leaf 1485907251) (.leaf 1453490663))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1421842893) (.branch 62 (.leaf 1390942558) (.leaf 1360769028))) (.branch 65 (.branch 64 (.leaf 1331302391) (.leaf 1302523424)) (.branch 66 (.leaf 1274413557) (.leaf 1246954853)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1220129971) (.leaf 1193922149)) (.branch 70 (.leaf 1168315172) (.leaf 1143293357))) (.branch 73 (.branch 72 (.leaf 1118841522) (.leaf 1094944972)) (.branch 74 (.leaf 1071589479) (.leaf 1048761257))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1026446950) (.branch 77 (.leaf 1004633616) (.leaf 983308703))) (.branch 80 (.branch 79 (.leaf 962460044) (.leaf 942075833)) (.branch 81 (.leaf 922144618) (.leaf 902655284)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 883597040) (.leaf 864959410)) (.branch 85 (.leaf 846732220) (.leaf 828905585))) (.branch 88 (.branch 87 (.leaf 811469901) (.leaf 794415836)) (.branch 89 (.leaf 777734315) (.leaf 761416518)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 745453867) (.branch 92 (.leaf 729838018) (.leaf 714560853))) (.branch 95 (.branch 94 (.leaf 699614474) (.leaf 684991194)) (.branch 96 (.leaf 670683532) (.leaf 656684202)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 642986111) (.leaf 629582353)) (.branch 100 (.leaf 616466198) (.leaf 603631092))) (.branch 103 (.branch 102 (.leaf 591070648) (.leaf 578778642)) (.branch 104 (.leaf 566749010) (.leaf 554975837))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 543453361) (.leaf 532175960)) (.branch 108 (.leaf 521138154) (.leaf 510334598))) (.branch 111 (.branch 110 (.leaf 499760079) (.leaf 489409510)) (.branch 112 (.leaf 479277930) (.leaf 469360498)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 459652488) (.leaf 450149290)) (.branch 116 (.leaf 440846404) (.leaf 431739436))) (.branch 119 (.branch 118 (.leaf 422824099) (.leaf 414096205)) (.branch 120 (.leaf 405551667) (.leaf 397186491)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1123).prefactor = (1356937562346067/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1123).cutoff/(generalMeanRows 1123).c)).2 =
    (217086225567757/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1123).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1123).q*(generalMeanRows 1123).c/2-2 = (3253/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable349.value]
  have hcontinuation : (generalMeanRows 1123).q*(generalMeanRows 1123).cutoff/2-2 = (1572/671:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable374.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1123).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1123).criticalRate j.val*(generalMeanRows 1123).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1123).c*(generalMeanRows 1123).criticalPoint j.val)).2-
      (generalMeanRows 1123).J/2-(generalMeanRows 1123).error (generalMeanGrid j.val)+
      (generalMeanRows 1123).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1123).c)).2-
      (generalMeanRows 1123).J/2-(generalMeanRows 1123).error 4 := by
  have he : (generalMeanRows 1123).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1123) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1123)
    (generalMeanRows_prefactorDomain 1123) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1123

/-! Kernel-checked entropy margins for general spectral rectangle 1124. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1124
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6460010978) (.branch 2 (.leaf 6265238921) (.leaf 6078366508))) (.branch 5 (.branch 4 (.leaf 5898957100) (.leaf 5726605240)) (.branch 6 (.leaf 5560933888) (.leaf 5401591956)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5248252104) (.leaf 5100608760)) (.branch 10 (.leaf 4958376344) (.leaf 4821287663))) (.branch 13 (.branch 12 (.leaf 4689092466) (.leaf 4561556133)) (.branch 14 (.leaf 4438458480) (.leaf 4319592686))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4204764300) (.branch 17 (.leaf 4093790349) (.leaf 3986498511))) (.branch 20 (.branch 19 (.leaf 3882726369) (.leaf 3782320715)) (.branch 21 (.leaf 3685136926) (.leaf 3591038374)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3499895895) (.leaf 3411587296)) (.branch 25 (.leaf 3325996899) (.leaf 3243015118))) (.branch 28 (.branch 27 (.leaf 3162538073) (.leaf 3084467229)) (.branch 29 (.leaf 3008709064) (.leaf 2935174756)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2863779899) (.branch 32 (.leaf 2794444235) (.leaf 2727091403))) (.branch 35 (.branch 34 (.leaf 2661648716) (.leaf 2598046934)) (.branch 36 (.leaf 2536220076) (.leaf 2476105224)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2417642350) (.leaf 2360774157)) (.branch 40 (.leaf 2305445922) (.leaf 2251605356))) (.branch 43 (.branch 42 (.leaf 2199202469) (.leaf 2148189447)) (.branch 44 (.leaf 2098520532) (.leaf 2050151915))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2003041632) (.branch 47 (.leaf 1957149468) (.leaf 1912436864))) (.branch 50 (.branch 49 (.leaf 1868866835) (.leaf 1826403887)) (.branch 51 (.leaf 1785013945) (.leaf 1744664278)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1705323436) (.leaf 1666961184)) (.branch 55 (.leaf 1629548446) (.leaf 1593057246))) (.branch 58 (.branch 57 (.leaf 1557460657) (.leaf 1522732754)) (.branch 59 (.leaf 1488848559) (.leaf 1455784008))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1423515899) (.branch 62 (.leaf 1392021858) (.leaf 1361280302))) (.branch 65 (.branch 64 (.leaf 1331270398) (.leaf 1301972038)) (.branch 66 (.leaf 1273365801) (.leaf 1245432923)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1218155274) (.leaf 1191515326)) (.branch 70 (.leaf 1165496127) (.leaf 1140081282))) (.branch 73 (.branch 72 (.leaf 1115254925) (.leaf 1091001699)) (.branch 74 (.leaf 1067306736) (.leaf 1044155636))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1021534448) (.branch 77 (.leaf 999429653) (.leaf 977828150))) (.branch 80 (.branch 79 (.leaf 956717232) (.leaf 936084579)) (.branch 81 (.leaf 915918240) (.leaf 896206617)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 876938455) (.leaf 858102827)) (.branch 85 (.leaf 839689125) (.leaf 821687044))) (.branch 88 (.branch 87 (.leaf 804086575) (.leaf 786877993)) (.branch 89 (.leaf 770051846) (.leaf 753598947)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 737510363) (.branch 92 (.leaf 721777410) (.leaf 706391639))) (.branch 95 (.branch 94 (.leaf 691344832) (.leaf 676628994)) (.branch 96 (.leaf 662236344) (.leaf 648159309)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 634390517) (.leaf 620922791)) (.branch 100 (.leaf 607749140) (.leaf 594862760))) (.branch 103 (.branch 102 (.leaf 582257018) (.leaf 569925455)) (.branch 104 (.leaf 557861779) (.leaf 546059856))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 534513709) (.leaf 523217511)) (.branch 108 (.leaf 512165584) (.leaf 501352389))) (.branch 111 (.branch 110 (.leaf 490772527) (.leaf 480420732)) (.branch 112 (.leaf 470291869) (.leaf 460380927)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 450683020) (.leaf 441193381)) (.branch 116 (.leaf 431907356) (.leaf 422820407))) (.branch 119 (.branch 118 (.leaf 413928104) (.leaf 405226121)) (.branch 120 (.leaf 396710239) (.leaf 388376338)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1124).prefactor = (2824203703778981/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1124).cutoff/(generalMeanRows 1124).c)).2 =
    (26792370738617/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1124).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1124).q*(generalMeanRows 1124).c/2-2 = (663/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable325.value]
  have hcontinuation : (generalMeanRows 1124).q*(generalMeanRows 1124).cutoff/2-2 = (1572/671:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable374.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1124).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1124).criticalRate j.val*(generalMeanRows 1124).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1124).c*(generalMeanRows 1124).criticalPoint j.val)).2-
      (generalMeanRows 1124).J/2-(generalMeanRows 1124).error (generalMeanGrid j.val)+
      (generalMeanRows 1124).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1124).c)).2-
      (generalMeanRows 1124).J/2-(generalMeanRows 1124).error 4 := by
  have he : (generalMeanRows 1124).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1124) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1124)
    (generalMeanRows_prefactorDomain 1124) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1124

/-! Kernel-checked entropy margins for general spectral rectangle 1125. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1125
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6347162863) (.branch 2 (.leaf 6146287406) (.leaf 5953709496))) (.branch 5 (.branch 4 (.leaf 5768971611) (.leaf 5591648715)) (.branch 6 (.leaf 5421345383) (.leaf 5257693241)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5100348675) (.leaf 4948990776)) (.branch 10 (.leaf 4803319493) (.leaf 4663053967))) (.branch 13 (.branch 12 (.leaf 4527931025) (.leaf 4397703816)) (.branch 14 (.leaf 4272140580) (.leaf 4151023515))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4034147758) (.branch 17 (.leaf 3921320451) (.leaf 3812359882))) (.branch 20 (.branch 19 (.leaf 3707094707) (.leaf 3605363230)) (.branch 21 (.leaf 3507012746) (.leaf 3411898934)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3319885302) (.leaf 3230842670)) (.branch 25 (.leaf 3144648696) (.leaf 3061187441))) (.branch 28 (.branch 27 (.leaf 2980348958) (.leaf 2902028922)) (.branch 29 (.leaf 2826128280) (.leaf 2752552924)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2681213400) (.branch 32 (.leaf 2612024619) (.leaf 2544905608))) (.branch 35 (.branch 34 (.leaf 2479779260) (.leaf 2416572113)) (.branch 36 (.leaf 2355214143) (.leaf 2295638561)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2237781637) (.leaf 2181582527)) (.branch 40 (.leaf 2126983113) (.leaf 2073927852))) (.branch 43 (.branch 42 (.leaf 2022363640) (.leaf 1972239677)) (.branch 44 (.leaf 1923507348) (.leaf 1876120103))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1830033355) (.branch 47 (.leaf 1785204372) (.leaf 1741592186))) (.branch 50 (.branch 49 (.leaf 1699157502) (.leaf 1657862614)) (.branch 51 (.leaf 1617671323) (.leaf 1578548868)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1540461850) (.leaf 1503378169)) (.branch 55 (.leaf 1467266958) (.leaf 1432098530))) (.branch 58 (.branch 57 (.leaf 1397844317) (.leaf 1364476819)) (.branch 59 (.leaf 1331969554) (.leaf 1300297014))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1269434616) (.branch 62 (.leaf 1239358665) (.leaf 1210046308))) (.branch 65 (.branch 64 (.leaf 1181475505) (.leaf 1153624985)) (.branch 66 (.leaf 1126474218) (.leaf 1100003380)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1074193325) (.leaf 1049025554)) (.branch 70 (.leaf 1024482190) (.leaf 1000545950))) (.branch 73 (.branch 72 (.leaf 977200122) (.leaf 954428541)) (.branch 74 (.leaf 932215567) (.leaf 910546064))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 889405379) (.branch 77 (.leaf 868779325) (.leaf 848654161))) (.branch 80 (.branch 79 (.leaf 829016575) (.leaf 809853667)) (.branch 81 (.leaf 791152935) (.leaf 772902260)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 755089889) (.leaf 737704423)) (.branch 85 (.leaf 720734805) (.leaf 704170306))) (.branch 88 (.branch 87 (.leaf 688000516) (.leaf 672215326)) (.branch 89 (.leaf 656804927) (.leaf 641759788)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 627070659) (.branch 92 (.leaf 612728548) (.leaf 598724725))) (.branch 95 (.branch 94 (.leaf 585050702) (.leaf 571698232)) (.branch 96 (.leaf 558659298) (.leaf 545926107)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 533491080) (.leaf 521346847)) (.branch 100 (.leaf 509486240) (.leaf 497902286))) (.branch 103 (.branch 102 (.leaf 486588201) (.leaf 475537385)) (.branch 104 (.leaf 464743413) (.leaf 454200034))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443901161) (.leaf 433840870)) (.branch 108 (.leaf 424013393) (.leaf 414413113))) (.branch 111 (.branch 110 (.leaf 405034559) (.leaf 395872405)) (.branch 112 (.leaf 386921460) (.leaf 378176670)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 369633110) (.leaf 361285982)) (.branch 116 (.leaf 353130608) (.leaf 345162433))) (.branch 119 (.branch 118 (.leaf 337377015) (.leaf 329770025)) (.branch 120 (.leaf 322337245) (.leaf 315074560)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1125).prefactor = (2939017528060997/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1125).cutoff/(generalMeanRows 1125).c)).2 =
    (406996865756549/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1125).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1125).q*(generalMeanRows 1125).cutoff/2-2 = (1572/671:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable374.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1125).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1125).criticalRate j.val*(generalMeanRows 1125).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1125).c*(generalMeanRows 1125).criticalPoint j.val)).2-
      (generalMeanRows 1125).J/2-(generalMeanRows 1125).error (generalMeanGrid j.val)+
      (generalMeanRows 1125).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1125).c)).2-
      (generalMeanRows 1125).J/2-(generalMeanRows 1125).error 4 := by
  have he : (generalMeanRows 1125).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1125) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1125)
    (generalMeanRows_prefactorDomain 1125) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1125

/-! Kernel-checked entropy margins for general spectral rectangle 1126. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1126
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6266317458) (.branch 2 (.leaf 6079608245) (.leaf 5900464232))) (.branch 5 (.branch 4 (.leaf 5728462102) (.leaf 5563209179)) (.branch 6 (.leaf 5404340699) (.leaf 5251517372)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5104423203) (.leaf 4962763535)) (.branch 10 (.leaf 4826263291) (.leaf 4694665390))) (.branch 13 (.branch 12 (.leaf 4567729315) (.leaf 4445229814)) (.branch 14 (.leaf 4326955728) (.leaf 4212708920))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4102303300) (.branch 17 (.leaf 3995563943) (.leaf 3892326273))) (.branch 20 (.branch 19 (.leaf 3792435325) (.leaf 3695745064)) (.branch 21 (.leaf 3602117763) (.leaf 3511423426)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3423539270) (.leaf 3338349231)) (.branch 25 (.leaf 3255743522) (.leaf 3175618221))) (.branch 28 (.branch 27 (.leaf 3097874887) (.leaf 3022420207)) (.branch 29 (.leaf 2949165676) (.leaf 2878027286)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2808925254) (.branch 32 (.leaf 2741783753) (.leaf 2676530681))) (.branch 35 (.branch 34 (.leaf 2613097427) (.leaf 2551418668)) (.branch 36 (.leaf 2491432171) (.leaf 2433078614)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2376301418) (.leaf 2321046586)) (.branch 40 (.leaf 2267262559) (.leaf 2214900077))) (.branch 43 (.branch 42 (.leaf 2163912053) (.leaf 2114253450)) (.branch 44 (.leaf 2065881171) (.leaf 2018753952))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1972832265) (.branch 47 (.leaf 1928078226) (.leaf 1884455507))) (.branch 50 (.branch 49 (.leaf 1841929256) (.leaf 1800466020)) (.branch 51 (.leaf 1760033675) (.leaf 1720601357)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1682139398) (.leaf 1644619270)) (.branch 55 (.leaf 1608013525) (.leaf 1572295748))) (.branch 58 (.branch 57 (.leaf 1537440500) (.leaf 1503423276)) (.branch 59 (.leaf 1470220462) (.leaf 1437809288))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1406167795) (.branch 62 (.leaf 1375274793) (.leaf 1345109831))) (.branch 65 (.branch 64 (.leaf 1315653158) (.leaf 1286885698)) (.branch 66 (.leaf 1258789013) (.leaf 1231345284)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1204537277) (.leaf 1178348323)) (.branch 70 (.leaf 1152762290) (.leaf 1127763564))) (.branch 73 (.branch 72 (.leaf 1103337025) (.leaf 1079468031)) (.branch 74 (.leaf 1056142391) (.leaf 1033346356))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1011066595) (.branch 77 (.leaf 989290182) (.leaf 968004577))) (.branch 80 (.branch 79 (.leaf 947197615) (.leaf 926857490)) (.branch 81 (.leaf 906972740) (.leaf 887532238)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 868525175) (.leaf 849941052)) (.branch 85 (.leaf 831769668) (.leaf 814001106))) (.branch 88 (.branch 87 (.leaf 796625730) (.leaf 779634169)) (.branch 89 (.leaf 763017308) (.leaf 746766285)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 730872474) (.branch 92 (.leaf 715327486) (.leaf 700123152))) (.branch 95 (.branch 94 (.leaf 685251524) (.leaf 670704863)) (.branch 96 (.leaf 656475632) (.leaf 642556491)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 628940293) (.leaf 615620073)) (.branch 100 (.leaf 602589045) (.leaf 589840597))) (.branch 103 (.branch 102 (.leaf 577368285) (.leaf 565165826)) (.branch 104 (.leaf 553227098) (.leaf 541546129))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 530117096) (.leaf 518934323)) (.branch 108 (.leaf 507992271) (.leaf 497285538))) (.branch 111 (.branch 110 (.leaf 486808854) (.leaf 476557077)) (.branch 112 (.leaf 466525189) (.leaf 456708296)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 447101617) (.leaf 437700490)) (.branch 116 (.leaf 428500361) (.leaf 419496787))) (.branch 119 (.branch 118 (.leaf 410685427) (.leaf 402062045)) (.branch 120 (.leaf 393622504) (.leaf 385362764)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1126).prefactor = (5521375740540297/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1126).cutoff/(generalMeanRows 1126).c)).2 =
    (229446619213911/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1126).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1126).q*(generalMeanRows 1126).c/2-2 = (6631/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable375.value]
  have hcontinuation : (generalMeanRows 1126).q*(generalMeanRows 1126).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1126).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1126).criticalRate j.val*(generalMeanRows 1126).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1126).c*(generalMeanRows 1126).criticalPoint j.val)).2-
      (generalMeanRows 1126).J/2-(generalMeanRows 1126).error (generalMeanGrid j.val)+
      (generalMeanRows 1126).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1126).c)).2-
      (generalMeanRows 1126).J/2-(generalMeanRows 1126).error 4 := by
  have he : (generalMeanRows 1126).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1126) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1126)
    (generalMeanRows_prefactorDomain 1126) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1126

/-! Kernel-checked entropy margins for general spectral rectangle 1127. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1127
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6593332085) (.branch 2 (.leaf 6399348882) (.leaf 6213190535))) (.branch 5 (.branch 4 (.leaf 6034418771) (.leaf 5862627088)) (.branch 6 (.leaf 5697437928) (.leaf 5538500143)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5385486736) (.leaf 5238092829)) (.branch 10 (.leaf 5096033843) (.leaf 4959043851))) (.branch 13 (.branch 12 (.leaf 4826874089) (.leaf 4699291618)) (.branch 14 (.leaf 4576078098) (.leaf 4457028683))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4341951008) (.branch 17 (.leaf 4230664273) (.leaf 4122998398))) (.branch 20 (.branch 19 (.leaf 4018793256) (.leaf 3917897969)) (.branch 21 (.leaf 3820170257) (.leaf 3725475853)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3633687945) (.leaf 3544686686)) (.branch 25 (.leaf 3458358720) (.leaf 3374596759))) (.branch 28 (.branch 27 (.leaf 3293299188) (.leaf 3214369698)) (.branch 29 (.leaf 3137716950) (.leaf 3063254258)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2990899301) (.branch 32 (.leaf 2920573856) (.leaf 2852203542))) (.branch 35 (.branch 34 (.leaf 2785717591) (.leaf 2721048630)) (.branch 36 (.leaf 2658132482) (.leaf 2596907975)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2537316770) (.leaf 2479303195)) (.branch 40 (.leaf 2422814095) (.leaf 2367798689))) (.branch 43 (.branch 42 (.leaf 2314208439) (.leaf 2261996921)) (.branch 44 (.leaf 2211119715) (.leaf 2161534290))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2113199908) (.branch 47 (.leaf 2066077523) (.leaf 2020129697))) (.branch 50 (.branch 49 (.leaf 1975320511) (.leaf 1931615489)) (.branch 51 (.leaf 1888981524) (.leaf 1847386809)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1806800767) (.leaf 1767193997)) (.branch 55 (.leaf 1728538209) (.leaf 1690806177))) (.branch 58 (.branch 57 (.leaf 1653971680) (.leaf 1618009458)) (.branch 59 (.leaf 1582895168) (.leaf 1548605337))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1515117325) (.branch 62 (.leaf 1482409283) (.leaf 1450460121))) (.branch 65 (.branch 64 (.leaf 1419249472) (.leaf 1388757659)) (.branch 66 (.leaf 1358965667) (.leaf 1329855112)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1301408213) (.leaf 1273607768)) (.branch 70 (.leaf 1246437130) (.leaf 1219880184))) (.branch 73 (.branch 72 (.leaf 1193921320) (.leaf 1168545419)) (.branch 74 (.leaf 1143737829) (.leaf 1119484349))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1095771208) (.branch 77 (.leaf 1072585051) (.leaf 1049912919))) (.branch 80 (.branch 79 (.leaf 1027742239) (.leaf 1006060806)) (.branch 81 (.leaf 984856769) (.leaf 964118618)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 943835174) (.leaf 923995574)) (.branch 85 (.leaf 904589259) (.leaf 885605967))) (.branch 88 (.branch 87 (.leaf 867035719) (.leaf 848868810)) (.branch 89 (.leaf 831095800) (.leaf 813707504)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 796694985) (.branch 92 (.leaf 780049545) (.leaf 763762714))) (.branch 95 (.branch 94 (.leaf 747826249) (.leaf 732232119)) (.branch 96 (.leaf 716972505) (.leaf 702039787)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 687426544) (.leaf 673125542)) (.branch 100 (.leaf 659129731) (.leaf 645432241))) (.branch 103 (.branch 102 (.leaf 632026373) (.leaf 618905593)) (.branch 104 (.leaf 606063534) (.leaf 593493984))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 581190882) (.leaf 569148318)) (.branch 108 (.leaf 557360525) (.leaf 545821876))) (.branch 111 (.branch 110 (.leaf 534526880) (.leaf 523470176)) (.branch 112 (.leaf 512646535) (.leaf 502050848)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 491678132) (.leaf 481523518)) (.branch 116 (.leaf 471582254) (.leaf 461849699))) (.branch 119 (.branch 118 (.leaf 452321318) (.leaf 442992686)) (.branch 120 (.leaf 433859477) (.leaf 424917468)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1127).prefactor = (5725996296051141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1127).cutoff/(generalMeanRows 1127).c)).2 =
    (46429865699473/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1127).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1127).q*(generalMeanRows 1127).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1127).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1127).criticalRate j.val*(generalMeanRows 1127).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1127).c*(generalMeanRows 1127).criticalPoint j.val)).2-
      (generalMeanRows 1127).J/2-(generalMeanRows 1127).error (generalMeanGrid j.val)+
      (generalMeanRows 1127).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1127).c)).2-
      (generalMeanRows 1127).J/2-(generalMeanRows 1127).error 4 := by
  have he : (generalMeanRows 1127).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1127) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1127)
    (generalMeanRows_prefactorDomain 1127) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1127

/-! Kernel-checked entropy margins for general spectral rectangle 1128. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1128
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7039180086) (.branch 2 (.leaf 6837363598) (.leaf 6643617416))) (.branch 5 (.branch 4 (.leaf 6457488477) (.leaf 6278556675)) (.branch 6 (.leaf 6106431907) (.leaf 5940751456)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5781177635) (.leaf 5627395688)) (.branch 10 (.leaf 5479111888) (.leaf 5336051838))) (.branch 13 (.branch 12 (.leaf 5197958921) (.leaf 5064592907)) (.branch 14 (.leaf 4935728688) (.leaf 4811155126))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4690674003) (.branch 17 (.leaf 4574099071) (.leaf 4461255174))) (.branch 20 (.branch 19 (.leaf 4351977453) (.leaf 4246110612)) (.branch 21 (.leaf 4143508254) (.leaf 4044032255)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3947552205) (.leaf 3853944887)) (.branch 25 (.leaf 3763093788) (.leaf 3674888666))) (.branch 28 (.branch 27 (.leaf 3589225132) (.leaf 3506004276)) (.branch 29 (.leaf 3425132314) (.leaf 3346520266)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3270083651) (.branch 32 (.leaf 3195742210) (.leaf 3123419650))) (.branch 35 (.branch 34 (.leaf 3053043394) (.leaf 2984544366)) (.branch 36 (.leaf 2917856779) (.leaf 2852917939)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2789668066) (.leaf 2728050126)) (.branch 40 (.leaf 2668009671) (.leaf 2609494692))) (.branch 43 (.branch 42 (.leaf 2552455487) (.leaf 2496844524)) (.branch 44 (.leaf 2442616329) (.leaf 2389727365))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2338135938) (.branch 47 (.leaf 2287802087) (.leaf 2238687499))) (.branch 50 (.branch 49 (.leaf 2190755420) (.leaf 2143970573)) (.branch 51 (.leaf 2098299082) (.leaf 2053708403)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2010167251) (.leaf 1967645544)) (.branch 55 (.leaf 1926114335) (.leaf 1885545764))) (.branch 58 (.branch 57 (.leaf 1845913001) (.leaf 1807190195)) (.branch 59 (.leaf 1769352433) (.leaf 1732375688))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1696236784) (.branch 62 (.leaf 1660913354) (.leaf 1626383803))) (.branch 65 (.branch 64 (.leaf 1592627272) (.leaf 1559623607)) (.branch 66 (.leaf 1527353328) (.leaf 1495797597)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1464938191) (.leaf 1434757477)) (.branch 70 (.leaf 1405238385) (.leaf 1376364385))) (.branch 73 (.branch 72 (.leaf 1348119465) (.leaf 1320488110)) (.branch 74 (.leaf 1293455280) (.leaf 1267006392))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1241127302) (.branch 77 (.leaf 1215804287) (.leaf 1191024028))) (.branch 80 (.branch 79 (.leaf 1166773599) (.leaf 1143040443)) (.branch 81 (.leaf 1119812368) (.leaf 1097077525)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1074824402) (.leaf 1053041808)) (.branch 85 (.leaf 1031718861) (.leaf 1010844978))) (.branch 88 (.branch 87 (.leaf 990409866) (.leaf 970403509)) (.branch 89 (.leaf 950816161) (.leaf 931638334)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 912860791) (.branch 92 (.leaf 894474538) (.leaf 876470815))) (.branch 95 (.branch 94 (.leaf 858841088) (.leaf 841577041)) (.branch 96 (.leaf 824670572) (.leaf 808113785)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 791898979) (.leaf 776018649)) (.branch 100 (.leaf 760465475) (.leaf 745232319))) (.branch 103 (.branch 102 (.leaf 730312217) (.leaf 715698375)) (.branch 104 (.leaf 701384165) (.leaf 687363119))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 673628923) (.leaf 660175417)) (.branch 108 (.leaf 646996583) (.leaf 634086549))) (.branch 111 (.branch 110 (.leaf 621439579) (.leaf 609050074)) (.branch 112 (.leaf 596912562) (.leaf 585021702)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 573372274) (.leaf 561959178)) (.branch 116 (.leaf 550777433) (.leaf 539822170))) (.branch 119 (.branch 118 (.leaf 529088632) (.leaf 518572168)) (.branch 120 (.leaf 508268235) (.leaf 498172388)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1128).prefactor = (2969100014481443/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1128).cutoff/(generalMeanRows 1128).c)).2 =
    (95039589490553/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1128).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1128).q*(generalMeanRows 1128).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1128).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1128).criticalRate j.val*(generalMeanRows 1128).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1128).c*(generalMeanRows 1128).criticalPoint j.val)).2-
      (generalMeanRows 1128).J/2-(generalMeanRows 1128).error (generalMeanGrid j.val)+
      (generalMeanRows 1128).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1128).c)).2-
      (generalMeanRows 1128).J/2-(generalMeanRows 1128).error 4 := by
  have he : (generalMeanRows 1128).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1128) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1128)
    (generalMeanRows_prefactorDomain 1128) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1128

/-! Kernel-checked entropy margins for general spectral rectangle 1129. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1129
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7515997411) (.branch 2 (.leaf 7306167120) (.leaf 7104657938))) (.branch 5 (.branch 4 (.leaf 6911001437) (.leaf 6724763370)) (.branch 6 (.leaf 6545540609) (.leaf 6372958422)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6206668034) (.leaf 6046344436)) (.branch 10 (.leaf 5891684423) (.leaf 5742404816))) (.branch 13 (.branch 12 (.leaf 5598240865) (.leaf 5458944798)) (.branch 14 (.leaf 5324284504) (.leaf 5194042343))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5068014052) (.branch 17 (.leaf 4946007760) (.leaf 4827843079))) (.branch 20 (.branch 19 (.leaf 4713350274) (.leaf 4602369509)) (.branch 21 (.leaf 4494750146) (.leaf 4390350108)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4289035293) (.leaf 4190679030)) (.branch 25 (.leaf 4095161580) (.leaf 4002369680))) (.branch 28 (.branch 27 (.leaf 3912196114) (.leaf 3824539322)) (.branch 29 (.leaf 3739303036) (.leaf 3656395944)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3575731375) (.branch 32 (.leaf 3497227017) (.leaf 3420804638))) (.branch 35 (.branch 34 (.leaf 3346389844) (.leaf 3273911845)) (.branch 36 (.leaf 3203303237) (.leaf 3134499802)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3067440322) (.leaf 3002066402)) (.branch 40 (.leaf 2938322309) (.leaf 2876154817))) (.branch 43 (.branch 42 (.leaf 2815513069) (.leaf 2756348441)) (.branch 44 (.leaf 2698614417) (.leaf 2642266477))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2587261985) (.branch 47 (.leaf 2533560087) (.leaf 2481121618))) (.branch 50 (.branch 49 (.leaf 2429909009) (.leaf 2379886206)) (.branch 51 (.leaf 2331018591) (.leaf 2283272907)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2236617187) (.leaf 2191020692)) (.branch 55 (.leaf 2146453849) (.leaf 2102888191))) (.branch 58 (.branch 57 (.leaf 2060296304) (.leaf 2018651777)) (.branch 59 (.leaf 1977929153) (.leaf 1938103881))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1899152279) (.branch 62 (.leaf 1861051486) (.leaf 1823779433))) (.branch 65 (.branch 64 (.leaf 1787314798) (.leaf 1751636978)) (.branch 66 (.leaf 1716726056) (.leaf 1682562768)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1649128476) (.leaf 1616405144)) (.branch 70 (.leaf 1584375306) (.leaf 1553022046))) (.branch 73 (.branch 72 (.leaf 1522328976) (.leaf 1492280209)) (.branch 74 (.leaf 1462860343) (.leaf 1434054441))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1405848010) (.branch 77 (.leaf 1378226985) (.leaf 1351177712))) (.branch 80 (.branch 79 (.leaf 1324686931) (.leaf 1298741762)) (.branch 81 (.leaf 1273329692) (.leaf 1248438558)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1224056536) (.leaf 1200172127)) (.branch 85 (.leaf 1176774148) (.leaf 1153851719))) (.branch 88 (.branch 87 (.leaf 1131394250) (.leaf 1109391436)) (.branch 89 (.leaf 1087833241) (.leaf 1066709896)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1046011881) (.branch 92 (.leaf 1025729925) (.leaf 1005854993))) (.branch 95 (.branch 94 (.leaf 986378279) (.leaf 967291199)) (.branch 96 (.leaf 948585384) (.leaf 930252674)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 912285108) (.leaf 894674922)) (.branch 100 (.leaf 877414540) (.leaf 860496570))) (.branch 103 (.branch 102 (.leaf 843913797) (.leaf 827659178)) (.branch 104 (.leaf 811725840) (.leaf 796107068))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 780796308) (.leaf 765787157)) (.branch 108 (.leaf 751073362) (.leaf 736648813))) (.branch 111 (.branch 110 (.leaf 722507542) (.leaf 708643717)) (.branch 112 (.leaf 695051637) (.leaf 681725732)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 668660558) (.leaf 655850790)) (.branch 116 (.leaf 643291226) (.leaf 630976776))) (.branch 119 (.branch 118 (.leaf 618902465) (.leaf 607063428)) (.branch 120 (.leaf 595454904) (.leaf 584072241)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1129).prefactor = (1231653593918423/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1129).cutoff/(generalMeanRows 1129).c)).2 =
    (60777167837797/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1129).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1129).q*(generalMeanRows 1129).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1129).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1129).criticalRate j.val*(generalMeanRows 1129).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1129).c*(generalMeanRows 1129).criticalPoint j.val)).2-
      (generalMeanRows 1129).J/2-(generalMeanRows 1129).error (generalMeanGrid j.val)+
      (generalMeanRows 1129).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1129).c)).2-
      (generalMeanRows 1129).J/2-(generalMeanRows 1129).error 4 := by
  have he : (generalMeanRows 1129).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1129) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1129)
    (generalMeanRows_prefactorDomain 1129) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1129

/-! Kernel-checked entropy margins for general spectral rectangle 1130. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1130
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8026908166) (.branch 2 (.leaf 7811904248) (.leaf 7605327425))) (.branch 5 (.branch 4 (.leaf 7406700930) (.leaf 7215582948)) (.branch 6 (.leaf 7031563490) (.leaf 6854261599)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6683322848) (.leaf 6518417100)) (.branch 10 (.leaf 6359236498) (.leaf 6205493643))) (.branch 13 (.branch 12 (.leaf 6056919957) (.leaf 5913264199)) (.branch 14 (.leaf 5774291116) (.leaf 5639780224))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5509524688) (.branch 17 (.leaf 5383330313) (.leaf 5261014613))) (.branch 20 (.branch 19 (.leaf 5142405964) (.leaf 5027342828)) (.branch 21 (.leaf 4915673040) (.leaf 4807253152)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4701947836) (.leaf 4599629326)) (.branch 25 (.leaf 4500176910) (.leaf 4403476460))) (.branch 28 (.branch 27 (.leaf 4309419994) (.leaf 4217905281)) (.branch 29 (.leaf 4128835459) (.leaf 4042118703)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3957667896) (.branch 32 (.leaf 3875400339) (.leaf 3795237473))) (.branch 35 (.branch 34 (.leaf 3717104629) (.leaf 3640930783)) (.branch 36 (.leaf 3566648344) (.leaf 3494192942)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3423503241) (.leaf 3354520758)) (.branch 40 (.leaf 3287189699) (.leaf 3221456801))) (.branch 43 (.branch 42 (.leaf 3157271191) (.leaf 3094584247)) (.branch 44 (.leaf 3033349475) (.leaf 2973522386))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2915060390) (.branch 47 (.leaf 2857922690) (.leaf 2802070186))) (.branch 50 (.branch 49 (.leaf 2747465382) (.leaf 2694072304)) (.branch 51 (.leaf 2641856415) (.leaf 2590784546)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2540824821) (.leaf 2491946593)) (.branch 55 (.leaf 2444120381) (.leaf 2397317810))) (.branch 58 (.branch 57 (.leaf 2351511560) (.leaf 2306675309)) (.branch 59 (.leaf 2262783689) (.leaf 2219812237))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2177737354) (.branch 62 (.leaf 2136536262) (.leaf 2096186966))) (.branch 65 (.branch 64 (.leaf 2056668221) (.leaf 2017959491)) (.branch 66 (.leaf 1980040924) (.leaf 1942893318)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1906498090) (.leaf 1870837255)) (.branch 70 (.leaf 1835893392) (.leaf 1801649627))) (.branch 73 (.branch 72 (.leaf 1768089607) (.leaf 1735197474)) (.branch 74 (.leaf 1702957854) (.leaf 1671355827))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1640376915) (.branch 77 (.leaf 1610007061) (.leaf 1580232616))) (.branch 80 (.branch 79 (.leaf 1551040319) (.leaf 1522417282)) (.branch 81 (.leaf 1494350980) (.leaf 1466829233)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1439840194) (.leaf 1413372338)) (.branch 85 (.leaf 1387414450) (.leaf 1361955611))) (.branch 88 (.branch 87 (.leaf 1336985192) (.leaf 1312492839)) (.branch 89 (.leaf 1288468467) (.leaf 1264902250)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1241784610) (.branch 92 (.leaf 1219106211) (.leaf 1196857949))) (.branch 95 (.branch 94 (.leaf 1175030947) (.leaf 1153616544)) (.branch 96 (.leaf 1132606292) (.leaf 1111991947)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1091765460) (.leaf 1071918977)) (.branch 100 (.leaf 1052444827) (.leaf 1033335521))) (.branch 103 (.branch 102 (.leaf 1014583744) (.leaf 996182349)) (.branch 104 (.leaf 978124356) (.leaf 960402940))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 943011436) (.leaf 925943327)) (.branch 108 (.leaf 909192240) (.leaf 892751948))) (.branch 111 (.branch 110 (.leaf 876616359) (.leaf 860779517)) (.branch 112 (.leaf 845235596) (.leaf 829978897)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 815003845) (.leaf 800304983)) (.branch 116 (.leaf 785876975) (.leaf 771714597))) (.branch 119 (.branch 118 (.leaf 757812735) (.leaf 744166386)) (.branch 120 (.leaf 730770650) (.leaf 717620732)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1130).prefactor = (393387771885161/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1130).cutoff/(generalMeanRows 1130).c)).2 =
    (251488755779919/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1130).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1130).q*(generalMeanRows 1130).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1130).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1130).criticalRate j.val*(generalMeanRows 1130).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1130).c*(generalMeanRows 1130).criticalPoint j.val)).2-
      (generalMeanRows 1130).J/2-(generalMeanRows 1130).error (generalMeanGrid j.val)+
      (generalMeanRows 1130).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1130).c)).2-
      (generalMeanRows 1130).J/2-(generalMeanRows 1130).error 4 := by
  have he : (generalMeanRows 1130).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1130) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1130)
    (generalMeanRows_prefactorDomain 1130) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1130

/-! Kernel-checked entropy margins for general spectral rectangle 1131. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1131
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5563957708) (.branch 2 (.leaf 5378029386) (.leaf 5200019657))) (.branch 5 (.branch 4 (.leaf 5029482354) (.leaf 4866003562)) (.branch 6 (.leaf 4709198745) (.leaf 4558710181)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4414204671) (.leaf 4275371479)) (.branch 10 (.leaf 4141920483) (.leaf 4013580502))) (.branch 13 (.branch 12 (.leaf 3890097792) (.leaf 3771234679)) (.branch 14 (.leaf 3656768319) (.leaf 3546489576))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3440201991) (.branch 17 (.leaf 3337720854) (.leaf 3238872349))) (.branch 20 (.branch 19 (.leaf 3143492768) (.leaf 3051427805)) (.branch 21 (.leaf 2962531893) (.leaf 2876667604)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2793705096) (.leaf 2713521604)) (.branch 25 (.leaf 2636000968) (.leaf 2561033200))) (.branch 28 (.branch 27 (.leaf 2488514085) (.leaf 2418344812)) (.branch 29 (.leaf 2350431627) (.leaf 2284685521)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2221021935) (.branch 32 (.leaf 2159360483) (.leaf 2099624706))) (.branch 35 (.branch 34 (.leaf 2041741829) (.leaf 1985642551)) (.branch 36 (.leaf 1931260831) (.leaf 1878533709)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1827401119) (.leaf 1777805733)) (.branch 40 (.leaf 1729692801) (.leaf 1683010011))) (.branch 43 (.branch 42 (.leaf 1637707353) (.leaf 1593736992)) (.branch 44 (.leaf 1551053154) (.leaf 1509612014))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1469371592) (.branch 47 (.leaf 1430291657) (.leaf 1392333639))) (.branch 50 (.branch 49 (.leaf 1355460540) (.leaf 1319636856)) (.branch 51 (.leaf 1284828503) (.leaf 1251002744)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1218128125) (.leaf 1186174410)) (.branch 55 (.leaf 1155112525) (.leaf 1124914502))) (.branch 58 (.branch 57 (.leaf 1095553425) (.leaf 1067003382)) (.branch 59 (.leaf 1039239418) (.leaf 1012237494))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 985974441) (.branch 62 (.leaf 960427923) (.leaf 935576402))) (.branch 65 (.branch 64 (.leaf 911399099) (.leaf 887875964)) (.branch 66 (.leaf 864987643) (.leaf 842715449)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 821041334) (.leaf 799947862)) (.branch 70 (.leaf 779418182) (.leaf 759436008))) (.branch 73 (.branch 72 (.leaf 739985592) (.leaf 721051704)) (.branch 74 (.leaf 702619611) (.leaf 684675059))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667204252) (.branch 77 (.leaf 650193835) (.leaf 633630878))) (.branch 80 (.branch 79 (.leaf 617502858) (.leaf 601797646)) (.branch 81 (.leaf 586503490) (.leaf 571609002)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 557103146) (.leaf 542975222)) (.branch 85 (.leaf 529214857) (.leaf 515811991))) (.branch 88 (.branch 87 (.leaf 502756869) (.leaf 490040027)) (.branch 89 (.leaf 477652281) (.leaf 465584723)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 453828705) (.branch 92 (.leaf 442375834) (.leaf 431217963))) (.branch 95 (.branch 94 (.leaf 420347182) (.leaf 409755808)) (.branch 96 (.leaf 399436382) (.leaf 389381658)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 379584600) (.leaf 370038368)) (.branch 100 (.leaf 360736319) (.leaf 351671999))) (.branch 103 (.branch 102 (.leaf 342839133) (.leaf 334231624)) (.branch 104 (.leaf 325843546) (.leaf 317669137))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 309702795) (.leaf 301939076)) (.branch 108 (.leaf 294372683) (.leaf 286998466))) (.branch 111 (.branch 110 (.leaf 279811418) (.leaf 272806668)) (.branch 112 (.leaf 265979478) (.leaf 259325239)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 252839467) (.leaf 246517801)) (.branch 116 (.leaf 240355997) (.leaf 234349924))) (.branch 119 (.branch 118 (.leaf 228495565) (.leaf 222789008)) (.branch 120 (.leaf 217226449) (.leaf 211804184)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1131).prefactor = (5765701042255661/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1131).cutoff/(generalMeanRows 1131).c)).2 =
    (17396961932593/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1131).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1131).q*(generalMeanRows 1131).c/2-2 = (397/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable376.value]
  have hcontinuation : (generalMeanRows 1131).q*(generalMeanRows 1131).cutoff/2-2 = (160/61:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable377.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1131).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1131).criticalRate j.val*(generalMeanRows 1131).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1131).c*(generalMeanRows 1131).criticalPoint j.val)).2-
      (generalMeanRows 1131).J/2-(generalMeanRows 1131).error (generalMeanGrid j.val)+
      (generalMeanRows 1131).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1131).c)).2-
      (generalMeanRows 1131).J/2-(generalMeanRows 1131).error 4 := by
  have he : (generalMeanRows 1131).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1131) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1131)
    (generalMeanRows_prefactorDomain 1131) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1131

/-! Kernel-checked entropy margins for general spectral rectangle 1132. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1132
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5657649098) (.branch 2 (.leaf 5468589932) (.leaf 5287582700))) (.branch 5 (.branch 4 (.leaf 5114173722) (.leaf 4947942114)) (.branch 6 (.leaf 4788496863) (.leaf 4635474225)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4488535389) (.leaf 4347364387)) (.branch 10 (.leaf 4211666212) (.leaf 4081165116))) (.branch 13 (.branch 12 (.leaf 3955603083) (.leaf 3834738436)) (.branch 14 (.leaf 3718344579) (.leaf 3606208854))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3498131494) (.branch 17 (.leaf 3393924679) (.leaf 3293411665))) (.branch 20 (.branch 19 (.leaf 3196425990) (.leaf 3102810746)) (.branch 21 (.leaf 3012417917) (.leaf 2925107761)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2840748249) (.leaf 2759214548)) (.branch 25 (.leaf 2680388543) (.leaf 2604158394))) (.branch 28 (.branch 27 (.leaf 2530418132) (.leaf 2459067279)) (.branch 29 (.leaf 2390010505) (.leaf 2323157302)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2258421686) (.branch 32 (.leaf 2195721918) (.leaf 2134980251))) (.branch 35 (.branch 34 (.leaf 2076122686) (.leaf 2019078752)) (.branch 36 (.leaf 1963781300) (.leaf 1910166306)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1858172695) (.leaf 1807742174)) (.branch 40 (.leaf 1758819069) (.leaf 1711350189))) (.branch 43 (.branch 42 (.leaf 1665284680) (.leaf 1620573903)) (.branch 44 (.leaf 1577171312) (.leaf 1535032345))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1494114315) (.branch 47 (.leaf 1454376314) (.leaf 1415779122))) (.branch 50 (.branch 49 (.leaf 1378285117) (.leaf 1341858199)) (.branch 51 (.leaf 1306463709) (.leaf 1272068358)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1238640164) (.leaf 1206148381)) (.branch 55 (.leaf 1174563445) (.leaf 1143856918))) (.branch 58 (.branch 57 (.leaf 1114001430) (.leaf 1084970634)) (.branch 59 (.leaf 1056739153) (.leaf 1029282544))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1002577248) (.branch 62 (.leaf 976600553) (.leaf 951330557))) (.branch 65 (.branch 64 (.leaf 926746133) (.leaf 902826892)) (.branch 66 (.leaf 879553155) (.leaf 856905920)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 834866835) (.leaf 813418170)) (.branch 70 (.leaf 792542792) (.leaf 772224138))) (.branch 73 (.branch 72 (.leaf 752446197) (.leaf 733193481)) (.branch 74 (.leaf 714451011) (.leaf 696204291))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 678439293) (.branch 77 (.leaf 661142438) (.leaf 644300578))) (.branch 80 (.branch 79 (.leaf 627900979) (.leaf 611931307)) (.branch 81 (.leaf 596379612) (.leaf 581234316)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 566484196) (.leaf 552118372)) (.branch 85 (.leaf 538126297) (.leaf 524497741))) (.branch 88 (.branch 87 (.leaf 511222784) (.leaf 498291803)) (.branch 89 (.leaf 485695460) (.leaf 473424696)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 461470719) (.branch 92 (.leaf 449824994) (.leaf 438479235))) (.branch 95 (.branch 94 (.leaf 427425401) (.leaf 416655679)) (.branch 96 (.leaf 406162484) (.leaf 395938450)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385976418) (.leaf 376269438)) (.branch 100 (.leaf 366810752) (.leaf 357593798))) (.branch 103 (.branch 102 (.leaf 348612196) (.leaf 339859745)) (.branch 104 (.leaf 331330420) (.leaf 323018362))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314917876) (.leaf 307023423)) (.branch 108 (.leaf 299329619) (.leaf 291831228))) (.branch 111 (.branch 110 (.leaf 284523158) (.leaf 277400455)) (.branch 112 (.leaf 270458302) (.leaf 263692012)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257097027) (.leaf 250668910)) (.branch 116 (.leaf 244403347) (.leaf 238296138))) (.branch 119 (.branch 118 (.leaf 232343198) (.leaf 226540549)) (.branch 120 (.leaf 220884322) (.leaf 215370751)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1132).prefactor = (5862789584638511/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1132).cutoff/(generalMeanRows 1132).c)).2 =
    (17396961932593/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1132).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1132).q*(generalMeanRows 1132).c/2-2 = (397/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable376.value]
  have hcontinuation : (generalMeanRows 1132).q*(generalMeanRows 1132).cutoff/2-2 = (160/61:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable377.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1132).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1132).criticalRate j.val*(generalMeanRows 1132).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1132).c*(generalMeanRows 1132).criticalPoint j.val)).2-
      (generalMeanRows 1132).J/2-(generalMeanRows 1132).error (generalMeanGrid j.val)+
      (generalMeanRows 1132).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1132).c)).2-
      (generalMeanRows 1132).J/2-(generalMeanRows 1132).error 4 := by
  have he : (generalMeanRows 1132).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1132) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1132)
    (generalMeanRows_prefactorDomain 1132) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1132

/-! Kernel-checked entropy margins for general spectral rectangle 1133. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1133
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6809868279) (.branch 2 (.leaf 6606367508) (.leaf 6411004158))) (.branch 5 (.branch 4 (.leaf 6223337914) (.leaf 6042959397)) (.branch 6 (.leaf 5869487426) (.leaf 5702566583)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5541865036) (.leaf 5387072587)) (.branch 10 (.leaf 5237898921) (.leaf 5094072023))) (.branch 13 (.branch 12 (.leaf 4955336752) (.leaf 4821453554)) (.branch 14 (.leaf 4692197285) (.leaf 4567356150))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4446730733) (.branch 17 (.leaf 4330133110) (.leaf 4217386045))) (.branch 20 (.branch 19 (.leaf 4108322243) (.leaf 4002783676)) (.branch 21 (.leaf 3900620955) (.leaf 3801692761)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3705865313) (.leaf 3613011880)) (.branch 25 (.leaf 3523012334) (.leaf 3435752729))) (.branch 28 (.branch 27 (.leaf 3351124921) (.leaf 3269026206)) (.branch 29 (.leaf 3189358994) (.leaf 3112030495)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3036952437) (.branch 32 (.leaf 2964040802) (.leaf 2893215570))) (.branch 35 (.branch 34 (.leaf 2824400499) (.leaf 2757522901)) (.branch 36 (.leaf 2692513445) (.leaf 2629305967)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2567837297) (.leaf 2508047092)) (.branch 40 (.leaf 2449877683) (.leaf 2393273932))) (.branch 43 (.branch 42 (.leaf 2338183096) (.leaf 2284554700)) (.branch 44 (.leaf 2232340416) (.leaf 2181493957))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2131970967) (.branch 47 (.leaf 2083728923) (.leaf 2036727042))) (.branch 50 (.branch 49 (.leaf 1990926198) (.leaf 1946288833)) (.branch 51 (.leaf 1902778883) (.leaf 1860361706)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1819004008) (.leaf 1778673786)) (.branch 55 (.leaf 1739340259) (.leaf 1700973814))) (.branch 58 (.branch 57 (.leaf 1663545950) (.leaf 1627029227)) (.branch 59 (.leaf 1591397216) (.leaf 1556624454))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1522686399) (.branch 62 (.leaf 1489559389) (.leaf 1457220603))) (.branch 65 (.branch 64 (.leaf 1425648022) (.leaf 1394820398)) (.branch 66 (.leaf 1364717215) (.leaf 1335318662)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1306605600) (.leaf 1278559534)) (.branch 70 (.leaf 1251162587) (.leaf 1224397473))) (.branch 73 (.branch 72 (.leaf 1198247473) (.leaf 1172696412)) (.branch 74 (.leaf 1147728636) (.leaf 1123328992))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1099482807) (.branch 77 (.leaf 1076175870) (.leaf 1053394412))) (.branch 80 (.branch 79 (.leaf 1031125091) (.leaf 1009354974)) (.branch 81 (.leaf 988071522) (.leaf 967262575)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 946916336) (.leaf 927021360)) (.branch 85 (.leaf 907566539) (.leaf 888541093))) (.branch 88 (.branch 87 (.leaf 869934551) (.leaf 851736747)) (.branch 89 (.leaf 833937806) (.leaf 816528134)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 799498407) (.branch 92 (.leaf 782839563) (.leaf 766542794))) (.branch 95 (.branch 94 (.leaf 750599533) (.leaf 735001451)) (.branch 96 (.leaf 719740444) (.leaf 704808631)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 690198340) (.leaf 675902107)) (.branch 100 (.leaf 661912666) (.leaf 648222943))) (.branch 103 (.branch 102 (.leaf 634826050) (.leaf 621715281)) (.branch 104 (.leaf 608884101) (.leaf 596326148))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 584035219) (.leaf 572005274)) (.branch 108 (.leaf 560230425) (.leaf 548704931))) (.branch 111 (.branch 110 (.leaf 537423198) (.leaf 526379773)) (.branch 112 (.leaf 515569335) (.leaf 504986699)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 494626805) (.leaf 484484720)) (.branch 116 (.leaf 474555630) (.leaf 464834837))) (.branch 119 (.branch 118 (.leaf 455317760) (.leaf 445999927)) (.branch 120 (.leaf 436876973) (.leaf 427944637)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1133).prefactor = (2851353941702541/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1133).cutoff/(generalMeanRows 1133).c)).2 =
    (392932271105719/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1133).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1133).q*(generalMeanRows 1133).c/2-2 = (1607/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable174.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1133).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1133).criticalRate j.val*(generalMeanRows 1133).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1133).c*(generalMeanRows 1133).criticalPoint j.val)).2-
      (generalMeanRows 1133).J/2-(generalMeanRows 1133).error (generalMeanGrid j.val)+
      (generalMeanRows 1133).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1133).c)).2-
      (generalMeanRows 1133).J/2-(generalMeanRows 1133).error 4 := by
  have he : (generalMeanRows 1133).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1133) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1133)
    (generalMeanRows_prefactorDomain 1133) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1133

/-! Kernel-checked entropy margins for general spectral rectangle 1134. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1134
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6459919572) (.branch 2 (.leaf 6274472505) (.leaf 6096383588))) (.branch 5 (.branch 4 (.leaf 5925248454) (.leaf 5760691571)) (.branch 6 (.leaf 5602363682) (.leaf 5449939525)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5303115794) (.leaf 5161609306)) (.branch 10 (.leaf 5025155364) (.leaf 4893506272))) (.branch 13 (.branch 12 (.leaf 4766429997) (.leaf 4643708961)) (.branch 14 (.leaf 4525138941) (.leaf 4410528070))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4299695928) (.branch 17 (.leaf 4192472713) (.leaf 4088698483))) (.branch 20 (.branch 19 (.leaf 3988222460) (.leaf 3890902398)) (.branch 21 (.leaf 3796603995) (.leaf 3705200357)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3616571505) (.leaf 3530603918)) (.branch 25 (.leaf 3447190112) (.leaf 3366228255))) (.branch 28 (.branch 27 (.leaf 3287621801) (.leaf 3211279166)) (.branch 29 (.leaf 3137113410) (.leaf 3065041959)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2994986334) (.branch 32 (.leaf 2926871907) (.leaf 2860627671))) (.branch 35 (.branch 34 (.leaf 2796186024) (.leaf 2733482571)) (.branch 36 (.leaf 2672455941) (.leaf 2613047607)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2555201733) (.leaf 2498865013)) (.branch 40 (.leaf 2443986539) (.leaf 2390517661))) (.branch 43 (.branch 42 (.leaf 2338411869) (.leaf 2287624673)) (.branch 44 (.leaf 2238113495) (.leaf 2189837570))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2142757846) (.branch 47 (.leaf 2096836898) (.leaf 2052038839))) (.branch 50 (.branch 49 (.leaf 2008329248) (.leaf 1965675087)) (.branch 51 (.leaf 1924044637) (.leaf 1883407430)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1843734186) (.leaf 1804996756)) (.branch 55 (.leaf 1767168067) (.leaf 1730222067))) (.branch 58 (.branch 57 (.leaf 1694133680) (.leaf 1658878756)) (.branch 59 (.leaf 1624434032) (.leaf 1590777085))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1557886297) (.branch 62 (.leaf 1525740818) (.leaf 1494320529))) (.branch 65 (.branch 64 (.leaf 1463606010) (.leaf 1433578511)) (.branch 66 (.leaf 1404219917) (.leaf 1375512728)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1347440025) (.leaf 1319985448)) (.branch 70 (.leaf 1293133173) (.leaf 1266867889))) (.branch 73 (.branch 72 (.leaf 1241174776) (.leaf 1216039483)) (.branch 74 (.leaf 1191448112) (.leaf 1167387198))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1143843692) (.branch 77 (.leaf 1120804944) (.leaf 1098258685))) (.branch 80 (.branch 79 (.leaf 1076193017) (.leaf 1054596397)) (.branch 81 (.leaf 1033457618) (.leaf 1012765806)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 992510397) (.leaf 972681134)) (.branch 85 (.leaf 953268051) (.leaf 934261464))) (.branch 88 (.branch 87 (.leaf 915651958) (.leaf 897430384)) (.branch 89 (.leaf 879587840) (.leaf 862115672)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 845005459) (.branch 92 (.leaf 828249006) (.leaf 811838337))) (.branch 95 (.branch 94 (.leaf 795765690) (.leaf 780023504)) (.branch 96 (.leaf 764604419) (.leaf 749501265)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 734707054) (.leaf 720214982)) (.branch 100 (.leaf 706018415) (.leaf 692110887))) (.branch 103 (.branch 102 (.leaf 678486094) (.leaf 665137891)) (.branch 104 (.leaf 652060285) (.leaf 639247430))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 626693623) (.leaf 614393301)) (.branch 108 (.leaf 602341035) (.leaf 590531528))) (.branch 111 (.branch 110 (.leaf 578959609) (.leaf 567620230)) (.branch 112 (.leaf 556508464) (.leaf 545619499)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 534948638) (.leaf 524491290)) (.branch 116 (.leaf 514242974) (.leaf 504199313))) (.branch 119 (.branch 118 (.leaf 494356029) (.leaf 484708942)) (.branch 120 (.leaf 475253970) (.leaf 465987121)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1134).prefactor = (2639987282904693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1134).cutoff/(generalMeanRows 1134).c)).2 =
    (86915796549789/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1134).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1134).q*(generalMeanRows 1134).c/2-2 = (3067/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable378.value]
  have hcontinuation : (generalMeanRows 1134).q*(generalMeanRows 1134).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable004.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1134).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1134).criticalRate j.val*(generalMeanRows 1134).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1134).c*(generalMeanRows 1134).criticalPoint j.val)).2-
      (generalMeanRows 1134).J/2-(generalMeanRows 1134).error (generalMeanGrid j.val)+
      (generalMeanRows 1134).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1134).c)).2-
      (generalMeanRows 1134).J/2-(generalMeanRows 1134).error 4 := by
  have he : (generalMeanRows 1134).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1134) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1134)
    (generalMeanRows_prefactorDomain 1134) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1134

/-! Kernel-checked entropy margins for general spectral rectangle 1135. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1135
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6576946380) (.branch 2 (.leaf 6383206590) (.leaf 6197218399))) (.branch 5 (.branch 4 (.leaf 6018556755) (.leaf 5846826824)) (.branch 6 (.leaf 5681661315) (.leaf 5522718085)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5369678013) (.leaf 5222243077)) (.branch 10 (.leaf 5080134640) (.leaf 4943091898))) (.branch 13 (.branch 12 (.leaf 4810870476) (.leaf 4683241167)) (.branch 14 (.leaf 4559988775) (.leaf 4440911075))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4325817857) (.branch 17 (.leaf 4214530059) (.leaf 4106878972))) (.branch 20 (.branch 19 (.leaf 4002705516) (.leaf 3901859568)) (.branch 21 (.leaf 3804199356) (.leaf 3709590896)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3617907467) (.leaf 3529029144)) (.branch 25 (.leaf 3442842348) (.leaf 3359239445))) (.branch 28 (.branch 27 (.leaf 3278118366) (.leaf 3199382262)) (.branch 29 (.leaf 3122939174) (.leaf 3048701739)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2976586910) (.branch 32 (.leaf 2906515695) (.leaf 2838412919))) (.branch 35 (.branch 34 (.leaf 2772206996) (.leaf 2707829724)) (.branch 36 (.leaf 2645216086) (.leaf 2584304072)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2525034506) (.leaf 2467350889)) (.branch 40 (.leaf 2411199249) (.leaf 2356528004))) (.branch 43 (.branch 42 (.leaf 2303287829) (.leaf 2251431539)) (.branch 44 (.leaf 2200913968) (.leaf 2151691868))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2103723805) (.branch 47 (.leaf 2056970065) (.leaf 2011392565))) (.branch 50 (.branch 49 (.leaf 1966954772) (.leaf 1923621622)) (.branch 51 (.leaf 1881359445) (.leaf 1840135901)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1799919907) (.leaf 1760681581)) (.branch 55 (.leaf 1722392184) (.leaf 1685024061))) (.branch 58 (.branch 57 (.leaf 1648550591) (.leaf 1612946141)) (.branch 59 (.leaf 1578186017) (.leaf 1544246418))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1511104403) (.branch 62 (.leaf 1478737844) (.leaf 1447125391))) (.branch 65 (.branch 64 (.leaf 1416246441) (.leaf 1386081101)) (.branch 66 (.leaf 1356610158) (.leaf 1327815050)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1299677836) (.leaf 1272181172)) (.branch 70 (.leaf 1245308286) (.leaf 1219042949))) (.branch 73 (.branch 72 (.leaf 1193369459) (.leaf 1168272614)) (.branch 74 (.leaf 1143737698) (.leaf 1119750452))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1096297063) (.branch 77 (.leaf 1073364147) (.leaf 1050938725))) (.branch 80 (.branch 79 (.leaf 1029008214) (.leaf 1007560410)) (.branch 81 (.leaf 986583470) (.leaf 966065904)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 945996556) (.leaf 926364599)) (.branch 85 (.leaf 907159513) (.leaf 888371084))) (.branch 88 (.branch 87 (.leaf 869989384) (.leaf 852004767)) (.branch 89 (.leaf 834407857) (.leaf 817189537)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 800340943) (.branch 92 (.leaf 783853453) (.leaf 767718678))) (.branch 95 (.branch 94 (.leaf 751928457) (.leaf 736474847)) (.branch 96 (.leaf 721350117) (.leaf 706546739)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 692057385) (.leaf 677874916)) (.branch 100 (.leaf 663992381) (.leaf 650403006))) (.branch 103 (.branch 102 (.leaf 637100191) (.leaf 624077505)) (.branch 104 (.leaf 611328680) (.leaf 598847605))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 586628323) (.leaf 574665024)) (.branch 108 (.leaf 562952046) (.leaf 551483861))) (.branch 111 (.branch 110 (.leaf 540255081) (.leaf 529260448)) (.branch 112 (.leaf 518494832) (.leaf 507953226)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 497630746) (.leaf 487522622)) (.branch 116 (.leaf 477624201) (.leaf 467930938))) (.branch 119 (.branch 118 (.leaf 458438397) (.leaf 449142246)) (.branch 120 (.leaf 440038254) (.leaf 431122290)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1135).prefactor = (5532869684269881/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1135).cutoff/(generalMeanRows 1135).c)).2 =
    (52929600774463/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1135).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1135).q*(generalMeanRows 1135).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable004.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1135).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1135).criticalRate j.val*(generalMeanRows 1135).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1135).c*(generalMeanRows 1135).criticalPoint j.val)).2-
      (generalMeanRows 1135).J/2-(generalMeanRows 1135).error (generalMeanGrid j.val)+
      (generalMeanRows 1135).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1135).c)).2-
      (generalMeanRows 1135).J/2-(generalMeanRows 1135).error 4 := by
  have he : (generalMeanRows 1135).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1135) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1135)
    (generalMeanRows_prefactorDomain 1135) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1135

/-! Kernel-checked entropy margins for general spectral rectangle 1136. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1136
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6508284059) (.branch 2 (.leaf 6306861158) (.leaf 6113640845))) (.branch 5 (.branch 4 (.leaf 5928174719) (.leaf 5750046070)) (.branch 6 (.leaf 5578867081) (.leaf 5414276324)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5255936535) (.leaf 5103532605)) (.branch 10 (.leaf 4956769783) (.leaf 4815372053))) (.branch 13 (.branch 12 (.leaf 4679080669) (.leaf 4547652825)) (.branch 14 (.leaf 4420860458) (.leaf 4298489144))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4180337108) (.branch 17 (.leaf 4066214314) (.leaf 3955941628))) (.branch 20 (.branch 19 (.leaf 3849350062) (.leaf 3746280074)) (.branch 21 (.leaf 3646580925) (.leaf 3550110093)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3456732727) (.leaf 3366321146)) (.branch 25 (.leaf 3278754380) (.leaf 3193917740))) (.branch 28 (.branch 27 (.leaf 3111702424) (.leaf 3032005150)) (.branch 29 (.leaf 2954727818) (.leaf 2879777191)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2807064609) (.branch 32 (.leaf 2736505711) (.leaf 2668020183))) (.branch 35 (.branch 34 (.leaf 2601531525) (.leaf 2536966828)) (.branch 36 (.leaf 2474256568) (.leaf 2413334419)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2354137069) (.leaf 2296604057)) (.branch 40 (.leaf 2240677613) (.leaf 2186302513))) (.branch 43 (.branch 42 (.leaf 2133425943) (.leaf 2081997367)) (.branch 44 (.leaf 2031968412) (.leaf 1983292746))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1935925982) (.branch 47 (.leaf 1889825570) (.leaf 1844950708))) (.branch 50 (.branch 49 (.leaf 1801262248) (.leaf 1758722623)) (.branch 51 (.leaf 1717295756) (.leaf 1676946998)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1637643051) (.leaf 1599351905)) (.branch 55 (.leaf 1562042777) (.leaf 1525686051))) (.branch 58 (.branch 57 (.leaf 1490253226) (.leaf 1455716859)) (.branch 59 (.leaf 1422050521) (.leaf 1389228748))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1357226999) (.branch 62 (.leaf 1326021611) (.leaf 1295589762))) (.branch 65 (.branch 64 (.leaf 1265909435) (.leaf 1236959381)) (.branch 66 (.leaf 1208719085) (.leaf 1181168736)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1154289196) (.leaf 1128061972)) (.branch 70 (.leaf 1102469187) (.leaf 1077493559))) (.branch 73 (.branch 72 (.leaf 1053118370) (.leaf 1029327449)) (.branch 74 (.leaf 1006105147) (.leaf 983436314))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 961306285) (.branch 77 (.leaf 939700853) (.leaf 918606259))) (.branch 80 (.branch 79 (.leaf 898009170) (.leaf 877896662)) (.branch 81 (.leaf 858256209) (.leaf 839075661)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 820343238) (.leaf 802047510)) (.branch 85 (.leaf 784177387) (.leaf 766722106))) (.branch 88 (.branch 87 (.leaf 749671217) (.leaf 733014578)) (.branch 89 (.leaf 716742337) (.leaf 700844924)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 685313045) (.branch 92 (.leaf 670137667) (.leaf 655310011))) (.branch 95 (.branch 94 (.leaf 640821546) (.leaf 626663975)) (.branch 96 (.leaf 612829233) (.leaf 599309476)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 586097074) (.leaf 573184605)) (.branch 100 (.leaf 560564847) (.leaf 548230773))) (.branch 103 (.branch 102 (.leaf 536175542) (.leaf 524392498)) (.branch 104 (.leaf 512875160) (.leaf 501617215))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 490612521) (.leaf 479855091)) (.branch 108 (.leaf 469339097) (.leaf 459058860))) (.branch 111 (.branch 110 (.leaf 449008847) (.leaf 439183669)) (.branch 112 (.leaf 429578072) (.leaf 420186936)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 411005272) (.leaf 402028215)) (.branch 116 (.leaf 393251024) (.leaf 384669076))) (.branch 119 (.branch 118 (.leaf 376277862) (.leaf 368072986)) (.branch 120 (.leaf 360050162) (.leaf 352205207)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1136).prefactor = (5797877728681811/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1136).cutoff/(generalMeanRows 1136).c)).2 =
    (401518120488057/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1136).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1136).q*(generalMeanRows 1136).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable004.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1136).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1136).criticalRate j.val*(generalMeanRows 1136).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1136).c*(generalMeanRows 1136).criticalPoint j.val)).2-
      (generalMeanRows 1136).J/2-(generalMeanRows 1136).error (generalMeanGrid j.val)+
      (generalMeanRows 1136).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1136).c)).2-
      (generalMeanRows 1136).J/2-(generalMeanRows 1136).error 4 := by
  have he : (generalMeanRows 1136).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1136) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1136)
    (generalMeanRows_prefactorDomain 1136) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1136

/-! Kernel-checked entropy margins for general spectral rectangle 1137. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1137
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6350756521) (.branch 2 (.leaf 6165765695) (.leaf 5988177181))) (.branch 5 (.branch 4 (.leaf 5817579816) (.leaf 5653592051)) (.branch 6 (.leaf 5495859318) (.leaf 5344051674)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5197861702) (.leaf 5057002620)) (.branch 10 (.leaf 4921206593) (.leaf 4790223194))) (.branch 13 (.branch 12 (.leaf 4663818035) (.leaf 4541771506)) (.branch 14 (.leaf 4423877652) (.leaf 4309943132))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4199786290) (.branch 17 (.leaf 4093236295) (.leaf 3990132356))) (.branch 20 (.branch 19 (.leaf 3890323015) (.leaf 3793665484)) (.branch 21 (.leaf 3700025047) (.leaf 3609274507)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3521293675) (.leaf 3435968906)) (.branch 25 (.leaf 3353192664) (.leaf 3272863123))) (.branch 28 (.branch 27 (.leaf 3194883799) (.leaf 3119163211)) (.branch 29 (.leaf 3045614562) (.leaf 2974155448)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2904707584) (.branch 32 (.leaf 2837196559) (.leaf 2771551591))) (.branch 35 (.branch 34 (.leaf 2707705319) (.leaf 2645593593)) (.branch 36 (.leaf 2585155291) (.leaf 2526332137)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2469068542) (.leaf 2413311446)) (.branch 40 (.leaf 2359010181) (.leaf 2306116331))) (.branch 43 (.branch 42 (.leaf 2254583610) (.leaf 2204367744)) (.branch 44 (.leaf 2155426362) (.leaf 2107718895))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2061206476) (.branch 47 (.leaf 2015851852) (.leaf 1971619302))) (.branch 50 (.branch 49 (.leaf 1928474550) (.leaf 1886384700)) (.branch 51 (.leaf 1845318158) (.leaf 1805244571)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1766134763) (.leaf 1727960675)) (.branch 55 (.leaf 1690695315) (.leaf 1654312701))) (.branch 58 (.branch 57 (.leaf 1618787816) (.leaf 1584096560)) (.branch 59 (.leaf 1550215707) (.leaf 1517122866))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1484796438) (.branch 62 (.leaf 1453215585) (.leaf 1422360193))) (.branch 65 (.branch 64 (.leaf 1392210837) (.leaf 1362748755)) (.branch 66 (.leaf 1333955816) (.leaf 1305814492)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1278307834) (.leaf 1251419446)) (.branch 70 (.leaf 1225133461) (.leaf 1199434520))) (.branch 73 (.branch 72 (.leaf 1174307752) (.leaf 1149738750)) (.branch 74 (.leaf 1125713556) (.leaf 1102218642))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1079240891) (.branch 77 (.leaf 1056767583) (.leaf 1034786380))) (.branch 80 (.branch 79 (.leaf 1013285308) (.leaf 992252745)) (.branch 81 (.leaf 971677411) (.leaf 951548348)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 931854914) (.leaf 912586769)) (.branch 85 (.leaf 893733864) (.leaf 875286433))) (.branch 88 (.branch 87 (.leaf 857234979) (.leaf 839570266)) (.branch 89 (.leaf 822283312) (.leaf 805365378)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 788807959) (.branch 92 (.leaf 772602779) (.leaf 756741782))) (.branch 95 (.branch 94 (.leaf 741217122) (.leaf 726021160)) (.branch 96 (.leaf 711146455) (.leaf 696585759)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 682332010) (.leaf 668378326)) (.branch 100 (.leaf 654717998) (.leaf 641344490))) (.branch 103 (.branch 102 (.leaf 628251426) (.leaf 615432590)) (.branch 104 (.leaf 602881922) (.leaf 590593508))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 578561583) (.leaf 566780519)) (.branch 108 (.leaf 555244827) (.leaf 543949150))) (.branch 111 (.branch 110 (.leaf 532888259) (.leaf 522057052)) (.branch 112 (.leaf 511450546) (.leaf 501063878)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 490892299) (.leaf 480931173)) (.branch 116 (.leaf 471175971) (.leaf 461622271))) (.branch 119 (.branch 118 (.leaf 452265752) (.leaf 443102195)) (.branch 120 (.leaf 434127476) (.leaf 425337569)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1137).prefactor = (1347267958282849/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1137).cutoff/(generalMeanRows 1137).c)).2 =
    (226736466054453/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1137).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1137).q*(generalMeanRows 1137).c/2-2 = (6387/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable379.value]
  have hcontinuation : (generalMeanRows 1137).q*(generalMeanRows 1137).cutoff/2-2 = (1565/651:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable380.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1137).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1137).criticalRate j.val*(generalMeanRows 1137).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1137).c*(generalMeanRows 1137).criticalPoint j.val)).2-
      (generalMeanRows 1137).J/2-(generalMeanRows 1137).error (generalMeanGrid j.val)+
      (generalMeanRows 1137).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1137).c)).2-
      (generalMeanRows 1137).J/2-(generalMeanRows 1137).error 4 := by
  have he : (generalMeanRows 1137).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1137) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1137)
    (generalMeanRows_prefactorDomain 1137) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1137

/-! Kernel-checked entropy margins for general spectral rectangle 1138. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1138
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6434580094) (.branch 2 (.leaf 6242353188) (.leaf 6057886262))) (.branch 5 (.branch 4 (.leaf 5880749126) (.leaf 5710542481)) (.branch 6 (.leaf 5546895172) (.leaf 5389461737)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5237920219) (.leaf 5091970197)) (.branch 10 (.leaf 4951331023) (.leaf 4815740230))) (.branch 13 (.branch 12 (.leaf 4684952088) (.leaf 4558736309)) (.branch 14 (.leaf 4436876860) (.leaf 4319170895))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4205427769) (.branch 17 (.leaf 4095468155) (.leaf 3989123222))) (.branch 20 (.branch 19 (.leaf 3886233893) (.leaf 3786650163)) (.branch 21 (.leaf 3690230467) (.leaf 3596841109)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3506355727) (.leaf 3418654807)) (.branch 25 (.leaf 3333625234) (.leaf 3251159872))) (.branch 28 (.branch 27 (.leaf 3171157182) (.leaf 3093520867)) (.branch 29 (.leaf 3018159539) (.leaf 2944986418)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2873919043) (.branch 32 (.leaf 2804879015) (.leaf 2737791747))) (.branch 35 (.branch 34 (.leaf 2672586240) (.leaf 2609194870)) (.branch 36 (.leaf 2547553189) (.leaf 2487599743)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2429275900) (.leaf 2372525690)) (.branch 40 (.leaf 2317295655) (.leaf 2263534707))) (.branch 43 (.branch 42 (.leaf 2211194002) (.leaf 2160226812)) (.branch 44 (.leaf 2110588416) (.leaf 2062235985))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2015128491) (.branch 47 (.leaf 1969226605) (.leaf 1924492609))) (.branch 50 (.branch 49 (.leaf 1880890317) (.leaf 1838384994)) (.branch 51 (.leaf 1796943281) (.leaf 1756533130)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1717123735) (.leaf 1678685472)) (.branch 55 (.leaf 1641189843) (.leaf 1604609420))) (.branch 58 (.branch 57 (.leaf 1568917794) (.leaf 1534089527)) (.branch 59 (.leaf 1500100106) (.leaf 1466925901))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1434544124) (.branch 62 (.leaf 1402932790) (.leaf 1372070680))) (.branch 65 (.branch 64 (.leaf 1341937310) (.leaf 1312512896)) (.branch 66 (.leaf 1283778321) (.leaf 1255715113)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1228305411) (.leaf 1201531941)) (.branch 70 (.leaf 1175377991) (.leaf 1149827389))) (.branch 73 (.branch 72 (.leaf 1124864479) (.leaf 1100474102)) (.branch 74 (.leaf 1076641572) (.leaf 1053352661))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1030593580) (.branch 77 (.leaf 1008350960) (.leaf 986611837))) (.branch 80 (.branch 79 (.leaf 965363636) (.leaf 944594157)) (.branch 81 (.leaf 924291559) (.leaf 904444350)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 885041370) (.leaf 866071781)) (.branch 85 (.leaf 847525055) (.leaf 829390964))) (.branch 88 (.branch 87 (.leaf 811659567) (.leaf 794321201)) (.branch 89 (.leaf 777366472) (.leaf 760786246)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 744571637) (.branch 92 (.leaf 728714002) (.leaf 713204932))) (.branch 95 (.branch 94 (.leaf 698036243) (.leaf 683199969)) (.branch 96 (.leaf 668688357) (.leaf 654493857)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 640609116) (.leaf 627026975)) (.branch 100 (.leaf 613740459) (.leaf 600742772))) (.branch 103 (.branch 102 (.leaf 588027292) (.leaf 575587569)) (.branch 104 (.leaf 563417312) (.leaf 551510392))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 539860832) (.leaf 528462805)) (.branch 108 (.leaf 517310628) (.leaf 506398761))) (.branch 111 (.branch 110 (.leaf 495721798) (.leaf 485274467)) (.branch 112 (.leaf 475051623) (.leaf 465048249)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 455259447) (.leaf 445680439)) (.branch 116 (.leaf 436306560) (.leaf 427133258))) (.branch 119 (.branch 118 (.leaf 418156091) (.leaf 409370719)) (.branch 120 (.leaf 400772907) (.leaf 392358521)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1138).prefactor = (5619689955288341/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1138).cutoff/(generalMeanRows 1138).c)).2 =
    (442632717556041/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1138).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1138).q*(generalMeanRows 1138).c/2-2 = (6631/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable375.value]
  have hcontinuation : (generalMeanRows 1138).q*(generalMeanRows 1138).cutoff/2-2 = (1565/651:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable380.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1138).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1138).criticalRate j.val*(generalMeanRows 1138).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1138).c*(generalMeanRows 1138).criticalPoint j.val)).2-
      (generalMeanRows 1138).J/2-(generalMeanRows 1138).error (generalMeanGrid j.val)+
      (generalMeanRows 1138).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1138).c)).2-
      (generalMeanRows 1138).J/2-(generalMeanRows 1138).error 4 := by
  have he : (generalMeanRows 1138).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1138) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1138)
    (generalMeanRows_prefactorDomain 1138) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1138

/-! Kernel-checked entropy margins for general spectral rectangle 1139. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1139
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6520254067) (.branch 2 (.leaf 6320624814) (.leaf 6129128100))) (.branch 5 (.branch 4 (.leaf 5945313764) (.leaf 5768763871)) (.branch 6 (.leaf 5599089851) (.leaf 5435929947)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5278946932) (.leaf 5127826064)) (.branch 10 (.leaf 4982273242) (.leaf 4842013348))) (.branch 13 (.branch 12 (.leaf 4706788751) (.leaf 4576357945)) (.branch 14 (.leaf 4450494319) (.leaf 4328985042))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4211630038) (.branch 17 (.leaf 4098241060) (.leaf 3988640837))) (.branch 20 (.branch 19 (.leaf 3882662301) (.leaf 3780147872)) (.branch 21 (.leaf 3680948803) (.leaf 3584924581)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3491942371) (.leaf 3401876512)) (.branch 25 (.leaf 3314608040) (.leaf 3230024257))) (.branch 28 (.branch 27 (.leaf 3148018332) (.leaf 3068488925)) (.branch 29 (.leaf 2991339847) (.leaf 2916479738)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2843821772) (.branch 32 (.leaf 2773283384) (.leaf 2704786011))) (.branch 35 (.branch 34 (.leaf 2638254858) (.leaf 2573618672)) (.branch 36 (.leaf 2510809541) (.leaf 2449762697)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2390416339) (.leaf 2332711464)) (.branch 40 (.leaf 2276591715) (.leaf 2222003226))) (.branch 43 (.branch 42 (.leaf 2168894493) (.leaf 2117216242)) (.branch 44 (.leaf 2066921310) (.leaf 2017964531))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1970302634) (.branch 47 (.leaf 1923894140) (.leaf 1878699271))) (.branch 50 (.branch 49 (.leaf 1834679862) (.leaf 1791799281)) (.branch 51 (.leaf 1750022348) (.leaf 1709315266)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1669645553) (.leaf 1630981973)) (.branch 55 (.leaf 1593294481) (.leaf 1556554163))) (.branch 58 (.branch 57 (.leaf 1520733182) (.leaf 1485804730)) (.branch 59 (.leaf 1451742975) (.leaf 1418523022))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1386120865) (.branch 62 (.leaf 1354513348) (.leaf 1323678131))) (.branch 65 (.branch 64 (.leaf 1293593647) (.leaf 1264239073)) (.branch 66 (.leaf 1235594294) (.leaf 1207639877)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1180357036) (.leaf 1153727609)) (.branch 70 (.leaf 1127734032) (.leaf 1102359310))) (.branch 73 (.branch 72 (.leaf 1077586998) (.leaf 1053401177)) (.branch 74 (.leaf 1029786430) (.leaf 1006727828))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 984210905) (.branch 77 (.leaf 962221643) (.leaf 940746454))) (.branch 80 (.branch 79 (.leaf 919772163) (.leaf 899285990)) (.branch 81 (.leaf 879275543) (.leaf 859728792)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 840634066) (.leaf 821980034)) (.branch 85 (.leaf 803755694) (.leaf 785950362))) (.branch 88 (.branch 87 (.leaf 768553660) (.leaf 751555504)) (.branch 89 (.leaf 734946097) (.leaf 718715915)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 702855701) (.branch 92 (.leaf 687356453) (.leaf 672209419))) (.branch 95 (.branch 94 (.leaf 657406086) (.leaf 642938171)) (.branch 96 (.leaf 628797617) (.leaf 614976583)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 601467437) (.leaf 588262751)) (.branch 100 (.leaf 575355293) (.leaf 562738023))) (.branch 103 (.branch 102 (.leaf 550404083) (.leaf 538346795)) (.branch 104 (.leaf 526559653) (.leaf 515036322))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 503770625) (.leaf 492756548)) (.branch 108 (.leaf 481988226) (.leaf 471459945))) (.branch 111 (.branch 110 (.leaf 461166135) (.leaf 451101365)) (.branch 112 (.leaf 441260341) (.leaf 431637902)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 422229012) (.leaf 413028763)) (.branch 116 (.leaf 404032367) (.leaf 395235153))) (.branch 119 (.branch 118 (.leaf 386632565) (.leaf 378220159)) (.branch 120 (.leaf 369993597) (.leaf 361948649)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1139).prefactor = (5860177071571539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1139).cutoff/(generalMeanRows 1139).c)).2 =
    (86381750838613/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1139).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1139).q*(generalMeanRows 1139).cutoff/2-2 = (1565/651:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable380.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1139).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1139).criticalRate j.val*(generalMeanRows 1139).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1139).c*(generalMeanRows 1139).criticalPoint j.val)).2-
      (generalMeanRows 1139).J/2-(generalMeanRows 1139).error (generalMeanGrid j.val)+
      (generalMeanRows 1139).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1139).c)).2-
      (generalMeanRows 1139).J/2-(generalMeanRows 1139).error 4 := by
  have he : (generalMeanRows 1139).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1139) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1139)
    (generalMeanRows_prefactorDomain 1139) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1139

/-! Kernel-checked entropy margins for general spectral rectangle 1140. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1140
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6307466626) (.branch 2 (.leaf 6124023131) (.leaf 5947931151))) (.branch 5 (.branch 4 (.leaf 5778777647) (.leaf 5616179730)) (.branch 6 (.leaf 5459781960) (.leaf 5309253941)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5164288159) (.leaf 5024598054)) (.branch 10 (.leaf 4889916280) (.leaf 4759993137))) (.branch 13 (.branch 12 (.leaf 4634595160) (.leaf 4513503837)) (.branch 14 (.leaf 4396514446) (.leaf 4283435003))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4174085298) (.branch 17 (.leaf 4068296026) (.leaf 3965907981))) (.branch 20 (.branch 19 (.leaf 3866771331) (.leaf 3770744944)) (.branch 21 (.leaf 3677695778) (.leaf 3587498318)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3500034056) (.leaf 3415191014)) (.branch 25 (.leaf 3332863310) (.leaf 3252950746))) (.branch 28 (.branch 27 (.leaf 3175358440) (.leaf 3099996479)) (.branch 29 (.leaf 3026779598) (.leaf 2955626887)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2886461515) (.branch 32 (.leaf 2819210474) (.leaf 2753804348))) (.branch 35 (.branch 34 (.leaf 2690177093) (.leaf 2628265828)) (.branch 36 (.leaf 2568010651) (.leaf 2509354463)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2452242801) (.leaf 2396623685)) (.branch 40 (.leaf 2342447478) (.leaf 2289666751))) (.branch 43 (.branch 42 (.leaf 2238236157) (.leaf 2188112320)) (.branch 44 (.leaf 2139253720) (.leaf 2091620596))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2045174850) (.branch 47 (.leaf 1999879957) (.leaf 1955700880))) (.branch 50 (.branch 49 (.leaf 1912603997) (.leaf 1870557022)) (.branch 51 (.leaf 1829528939) (.leaf 1789489937)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1750411351) (.leaf 1712265600)) (.branch 55 (.leaf 1675026140) (.leaf 1638667407))) (.branch 58 (.branch 57 (.leaf 1603164774) (.leaf 1568494505)) (.branch 59 (.leaf 1534633713) (.leaf 1501560318))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1469253015) (.branch 62 (.leaf 1437691232) (.leaf 1406855101))) (.branch 65 (.branch 64 (.leaf 1376725425) (.leaf 1347283650)) (.branch 66 (.leaf 1318511834) (.leaf 1290392622)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1262909221) (.leaf 1236045376)) (.branch 70 (.leaf 1209785348) (.leaf 1184113889))) (.branch 73 (.branch 72 (.leaf 1159016228) (.leaf 1134478046)) (.branch 74 (.leaf 1110485463) (.leaf 1087025014))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1064083640) (.branch 77 (.leaf 1041648666) (.leaf 1019707791))) (.branch 80 (.branch 79 (.leaf 998249072) (.leaf 977260907)) (.branch 81 (.leaf 956732031) (.leaf 936651493)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 917008653) (.leaf 897793168)) (.branch 85 (.leaf 878994979) (.leaf 860604305))) (.branch 88 (.branch 87 (.leaf 842611630) (.leaf 825007697)) (.branch 89 (.leaf 807783497) (.leaf 790930259)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 774439447) (.branch 92 (.leaf 758302748) (.leaf 742512067))) (.branch 95 (.branch 94 (.leaf 727059519) (.leaf 711937420)) (.branch 96 (.leaf 697138286) (.leaf 682654823)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 668479919) (.leaf 654606645)) (.branch 100 (.leaf 641028244) (.leaf 627738125))) (.branch 103 (.branch 102 (.leaf 614729863) (.leaf 601997191)) (.branch 104 (.leaf 589533995) (.leaf 577334310))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 565392317) (.leaf 553702336)) (.branch 108 (.leaf 542258824) (.leaf 531056373))) (.branch 111 (.branch 110 (.leaf 520089701) (.leaf 509353654)) (.branch 112 (.leaf 498843198) (.leaf 488553418)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 478479515) (.leaf 468616803)) (.branch 116 (.leaf 458960703) (.leaf 449506745))) (.branch 119 (.branch 118 (.leaf 440250560) (.leaf 431187881)) (.branch 120 (.leaf 422314539) (.leaf 413626461)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1140).prefactor = (436739733977/80000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1140).cutoff/(generalMeanRows 1140).c)).2 =
    (240349459181249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1140).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1140).q*(generalMeanRows 1140).c/2-2 = (13/16:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable042.value]
  have hcontinuation : (generalMeanRows 1140).q*(generalMeanRows 1140).cutoff/2-2 = (79/31:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable381.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1140).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1140).criticalRate j.val*(generalMeanRows 1140).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1140).c*(generalMeanRows 1140).criticalPoint j.val)).2-
      (generalMeanRows 1140).J/2-(generalMeanRows 1140).error (generalMeanGrid j.val)+
      (generalMeanRows 1140).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1140).c)).2-
      (generalMeanRows 1140).J/2-(generalMeanRows 1140).error 4 := by
  have he : (generalMeanRows 1140).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1140) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1140)
    (generalMeanRows_prefactorDomain 1140) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1140

/-! Kernel-checked entropy margins for general spectral rectangle 1141. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1141
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6457344347) (.branch 2 (.leaf 6267152362) (.leaf 6084616898))) (.branch 5 (.branch 4 (.leaf 5909308223) (.leaf 5740827923)) (.branch 6 (.leaf 5578806101) (.leaf 5422898872)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5272786129) (.leaf 5128169533)) (.branch 10 (.leaf 4988770715) (.leaf 4854329643))) (.branch 13 (.branch 12 (.leaf 4724603155) (.leaf 4599363635)) (.branch 14 (.leaf 4478397800) (.leaf 4361505609))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4248499266) (.branch 17 (.leaf 4139202309) (.leaf 4033448783))) (.branch 20 (.branch 19 (.leaf 3931082481) (.leaf 3831956245)) (.branch 21 (.leaf 3735931336) (.leaf 3642876842)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3552669145) (.leaf 3465191424)) (.branch 25 (.leaf 3380333200) (.leaf 3297989914))) (.branch 28 (.branch 27 (.leaf 3218062542) (.leaf 3140457231)) (.branch 29 (.leaf 3065084973) (.leaf 2991861293)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2920705965) (.branch 32 (.leaf 2851542751) (.leaf 2784299154))) (.branch 35 (.branch 34 (.leaf 2718906187) (.leaf 2655298169)) (.branch 36 (.leaf 2593412519) (.leaf 2533189579)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2474572444) (.leaf 2417506797)) (.branch 40 (.leaf 2361940766) (.leaf 2307824782))) (.branch 43 (.branch 42 (.leaf 2255111452) (.leaf 2203755438)) (.branch 44 (.leaf 2153713342) (.leaf 2104943601))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2057406390) (.branch 47 (.leaf 2011063526) (.leaf 1965878385))) (.branch 50 (.branch 49 (.leaf 1921815816) (.leaf 1878842068)) (.branch 51 (.leaf 1836924719) (.leaf 1796032604)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1756135758) (.leaf 1717205349)) (.branch 55 (.leaf 1679213630) (.leaf 1642133882))) (.branch 58 (.branch 57 (.leaf 1605940364) (.leaf 1570608267)) (.branch 59 (.leaf 1536113674) (.leaf 1502433510))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1469545513) (.branch 62 (.leaf 1437428189) (.leaf 1406060781))) (.branch 65 (.branch 64 (.leaf 1375423235) (.leaf 1345496171)) (.branch 66 (.leaf 1316260849) (.leaf 1287699147)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1259793530) (.leaf 1232527028)) (.branch 70 (.leaf 1205883211) (.leaf 1179846165))) (.branch 73 (.branch 72 (.leaf 1154400476) (.leaf 1129531203)) (.branch 74 (.leaf 1105223867) (.leaf 1081464424))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1058239254) (.branch 77 (.leaf 1035535144) (.leaf 1013339269))) (.branch 80 (.branch 79 (.leaf 991639181) (.leaf 970422792)) (.branch 81 (.leaf 949678364) (.leaf 929394493)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 909560097) (.leaf 890164407)) (.branch 85 (.leaf 871196953) (.leaf 852647556))) (.branch 88 (.branch 87 (.leaf 834506317) (.leaf 816763604)) (.branch 89 (.leaf 799410050) (.leaf 782436537)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 765834191) (.branch 92 (.leaf 749594375) (.leaf 733708678))) (.branch 95 (.branch 94 (.leaf 718168911) (.leaf 702967096)) (.branch 96 (.leaf 688095464) (.leaf 673546445)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 659312662) (.leaf 645386927)) (.branch 100 (.leaf 631762232) (.leaf 618431749))) (.branch 103 (.branch 102 (.leaf 605388817) (.leaf 592626943)) (.branch 104 (.leaf 580139796) (.leaf 567921199))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 555965128) (.leaf 544265708)) (.branch 108 (.leaf 532817203) (.leaf 521614021))) (.branch 111 (.branch 110 (.leaf 510650701) (.leaf 499921915)) (.branch 112 (.leaf 489422464) (.leaf 479147270)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 469091379) (.leaf 459249952)) (.branch 116 (.leaf 449618266) (.leaf 440191708))) (.branch 119 (.branch 118 (.leaf 430965773) (.leaf 421936063)) (.branch 120 (.leaf 413098281) (.leaf 404448229)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1141).prefactor = (5670080078977641/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1141).cutoff/(generalMeanRows 1141).c)).2 =
    (475379756884899/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1141).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1141).q*(generalMeanRows 1141).c/2-2 = (331/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable296.value]
  have hcontinuation : (generalMeanRows 1141).q*(generalMeanRows 1141).cutoff/2-2 = (79/31:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable381.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1141).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1141).criticalRate j.val*(generalMeanRows 1141).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1141).c*(generalMeanRows 1141).criticalPoint j.val)).2-
      (generalMeanRows 1141).J/2-(generalMeanRows 1141).error (generalMeanGrid j.val)+
      (generalMeanRows 1141).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1141).c)).2-
      (generalMeanRows 1141).J/2-(generalMeanRows 1141).error 4 := by
  have he : (generalMeanRows 1141).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1141) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1141)
    (generalMeanRows_prefactorDomain 1141) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1141

/-! Kernel-checked entropy margins for general spectral rectangle 1142. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1142
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6610949297) (.branch 2 (.leaf 6413789603) (.leaf 6224603494))) (.branch 5 (.branch 4 (.leaf 6042943852) (.leaf 5868396097)) (.branch 6 (.leaf 5700575268) (.leaf 5539123435)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5383707368) (.leaf 5234016461)) (.branch 10 (.leaf 5089760857) (.leaf 4950669758))) (.branch 13 (.branch 12 (.leaf 4816489901) (.leaf 4686984180)) (.branch 14 (.leaf 4561930392) (.leaf 4441120100))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4324357600) (.branch 17 (.leaf 4211458973) (.leaf 4102251230))) (.branch 20 (.branch 19 (.leaf 3996571518) (.leaf 3894266400)) (.branch 21 (.leaf 3795191198) (.leaf 3699209376)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3606191992) (.leaf 3516017175)) (.branch 25 (.leaf 3428569658) (.leaf 3343740336))) (.branch 28 (.branch 27 (.leaf 3261425868) (.leaf 3181528298)) (.branch 29 (.leaf 3103954716) (.leaf 3028616934)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2955431191) (.branch 32 (.leaf 2884317883) (.leaf 2815201302))) (.branch 35 (.branch 34 (.leaf 2748009402) (.leaf 2682673579)) (.branch 36 (.leaf 2619128468) (.leaf 2557311749)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2497163971) (.leaf 2438628386)) (.branch 40 (.leaf 2381650798) (.leaf 2326179412))) (.branch 43 (.branch 42 (.leaf 2272164706) (.leaf 2219559302)) (.branch 44 (.leaf 2168317849) (.leaf 2118396913))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2069754872) (.branch 47 (.leaf 2022351823) (.leaf 1976149491))) (.branch 50 (.branch 49 (.leaf 1931111140) (.leaf 1887201498)) (.branch 51 (.leaf 1844386681) (.leaf 1802634121)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1761912503) (.leaf 1722191701)) (.branch 55 (.leaf 1683442719) (.leaf 1645637641))) (.branch 58 (.branch 57 (.leaf 1608749571) (.leaf 1572752592)) (.branch 59 (.leaf 1537621716) (.leaf 1503332843))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1469862718) (.branch 62 (.leaf 1437188894) (.leaf 1405289695))) (.branch 65 (.branch 64 (.leaf 1374144181) (.leaf 1343732119)) (.branch 66 (.leaf 1314033947) (.leaf 1285030748)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1256704223) (.leaf 1229036664)) (.branch 70 (.leaf 1202010928) (.leaf 1175610417))) (.branch 73 (.branch 72 (.leaf 1149819052) (.leaf 1124621254)) (.branch 74 (.leaf 1100001925) (.leaf 1075946426))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1052440563) (.branch 77 (.leaf 1029470565) (.leaf 1007023072))) (.branch 80 (.branch 79 (.leaf 985085117) (.leaf 963644113)) (.branch 81 (.leaf 942687836) (.leaf 922204417)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 902182322) (.leaf 882610347)) (.branch 85 (.leaf 863477599) (.leaf 844773494))) (.branch 88 (.branch 87 (.leaf 826487736) (.leaf 808610317)) (.branch 89 (.leaf 791131500) (.leaf 774041811)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 757332034) (.branch 92 (.leaf 740993200) (.leaf 725016577))) (.branch 95 (.branch 94 (.leaf 709393665) (.leaf 694116187)) (.branch 96 (.leaf 679176083) (.leaf 664565504)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 650276801) (.leaf 636302525)) (.branch 100 (.leaf 622635415) (.leaf 609268396))) (.branch 103 (.branch 102 (.leaf 596194573) (.leaf 583407223)) (.branch 104 (.leaf 570899793) (.leaf 558665894))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 546699294) (.leaf 534993918)) (.branch 108 (.leaf 523543838) (.leaf 512343274))) (.branch 111 (.branch 110 (.leaf 501386586) (.leaf 490668271)) (.branch 112 (.leaf 480182961) (.leaf 469925416)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 459890525) (.leaf 450073295)) (.branch 116 (.leaf 440468858) (.leaf 431072459))) (.branch 119 (.branch 118 (.leaf 421879455) (.leaf 412885316)) (.branch 120 (.leaf 404085617) (.leaf 395476038)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1142).prefactor = (5889055764953539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1142).cutoff/(generalMeanRows 1142).c)).2 =
    (235044369625241/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1142).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1142).q*(generalMeanRows 1142).c/2-2 = (337/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable382.value]
  have hcontinuation : (generalMeanRows 1142).q*(generalMeanRows 1142).cutoff/2-2 = (79/31:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable381.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1142).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1142).criticalRate j.val*(generalMeanRows 1142).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1142).c*(generalMeanRows 1142).criticalPoint j.val)).2-
      (generalMeanRows 1142).J/2-(generalMeanRows 1142).error (generalMeanGrid j.val)+
      (generalMeanRows 1142).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1142).c)).2-
      (generalMeanRows 1142).J/2-(generalMeanRows 1142).error 4 := by
  have he : (generalMeanRows 1142).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1142) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1142)
    (generalMeanRows_prefactorDomain 1142) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1142

/-! Kernel-checked entropy margins for general spectral rectangle 1143. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1143
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7066825771) (.branch 2 (.leaf 6861297419) (.leaf 6664005635))) (.branch 5 (.branch 4 (.leaf 6474487654) (.leaf 6292314489)) (.branch 6 (.leaf 6117087912) (.leaf 5948437748)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5786019461) (.leaf 5629511993)) (.branch 10 (.leaf 5478615810) (.leaf 5333051153))) (.branch 13 (.branch 12 (.leaf 5192556450) (.leaf 5056886880)) (.branch 14 (.leaf 4925813076) (.leaf 4799119941))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4676605569) (.branch 17 (.leaf 4558080272) (.leaf 4443365678))) (.branch 20 (.branch 19 (.leaf 4332293915) (.leaf 4224706862)) (.branch 21 (.leaf 4120455460) (.leaf 4019399082)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3921404952) (.leaf 3826347613)) (.branch 25 (.leaf 3734108434) (.leaf 3644575155))) (.branch 28 (.branch 27 (.leaf 3557641472) (.leaf 3473206646)) (.branch 29 (.leaf 3391175148) (.leaf 3311456325)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3233964097) (.branch 32 (.leaf 3158616669) (.leaf 3085336267))) (.branch 35 (.branch 34 (.leaf 3014048894) (.leaf 2944684099)) (.branch 36 (.leaf 2877174771) (.leaf 2811456935)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2747469570) (.leaf 2685154441)) (.branch 40 (.leaf 2624455932) (.leaf 2565320906))) (.branch 43 (.branch 42 (.leaf 2507698557) (.leaf 2451540285)) (.branch 44 (.leaf 2396799573) (.leaf 2343431873))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2291394500) (.branch 47 (.leaf 2240646531) (.leaf 2191148713))) (.branch 50 (.branch 49 (.leaf 2142863374) (.leaf 2095754341)) (.branch 51 (.leaf 2049786866) (.leaf 2004927549)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1961144272) (.leaf 1918406135)) (.branch 55 (.leaf 1876683396) (.leaf 1835947417))) (.branch 58 (.branch 57 (.leaf 1796170604) (.leaf 1757326364)) (.branch 59 (.leaf 1719389053) (.leaf 1682333936))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1646137139) (.branch 62 (.leaf 1610775617) (.leaf 1576227108))) (.branch 65 (.branch 64 (.leaf 1542470105) (.leaf 1509483820)) (.branch 66 (.leaf 1477248150) (.leaf 1445743652)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1414951510) (.leaf 1384853514)) (.branch 70 (.leaf 1355432026) (.leaf 1326669968))) (.branch 73 (.branch 72 (.leaf 1298550786) (.leaf 1271058441)) (.branch 74 (.leaf 1244177377) (.leaf 1217892513))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1192189215) (.branch 77 (.leaf 1167053283) (.leaf 1142470936))) (.branch 80 (.branch 79 (.leaf 1118428790) (.leaf 1094913849)) (.branch 81 (.leaf 1071913491) (.leaf 1049415447)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1027407796) (.leaf 1005878948)) (.branch 85 (.leaf 984817636) (.leaf 964212899))) (.branch 88 (.branch 87 (.leaf 944054077) (.leaf 924330797)) (.branch 89 (.leaf 905032966) (.leaf 886150759)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 867674609) (.branch 92 (.leaf 849595205) (.leaf 831903476))) (.branch 95 (.branch 94 (.leaf 814590587) (.leaf 797647931)) (.branch 96 (.leaf 781067122) (.leaf 764839987)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 748958560) (.leaf 733415075)) (.branch 100 (.leaf 718201963) (.leaf 703311840))) (.branch 103 (.branch 102 (.leaf 688737507) (.leaf 674471942)) (.branch 104 (.leaf 660508295) (.leaf 646839884))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 633460188) (.leaf 620362844)) (.branch 108 (.leaf 607541642) (.leaf 594990522))) (.branch 111 (.branch 110 (.leaf 582703567) (.leaf 570675002)) (.branch 112 (.leaf 558899186) (.leaf 547370614)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 536083910) (.leaf 525033820)) (.branch 116 (.leaf 514215218) (.leaf 503623093))) (.branch 119 (.branch 118 (.leaf 493252551) (.leaf 483098811)) (.branch 120 (.leaf 473157203) (.leaf 463423162)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1143).prefactor = (6116488183529467/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1143).cutoff/(generalMeanRows 1143).c)).2 =
    (240349459181249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1143).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1143).q*(generalMeanRows 1143).c/2-2 = (13/16:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable042.value]
  have hcontinuation : (generalMeanRows 1143).q*(generalMeanRows 1143).cutoff/2-2 = (79/31:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable381.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1143).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1143).criticalRate j.val*(generalMeanRows 1143).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1143).c*(generalMeanRows 1143).criticalPoint j.val)).2-
      (generalMeanRows 1143).J/2-(generalMeanRows 1143).error (generalMeanGrid j.val)+
      (generalMeanRows 1143).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1143).c)).2-
      (generalMeanRows 1143).J/2-(generalMeanRows 1143).error 4 := by
  have he : (generalMeanRows 1143).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1143) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1143)
    (generalMeanRows_prefactorDomain 1143) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1143

/-! Kernel-checked entropy margins for general spectral rectangle 1144. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1144
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7665108919) (.branch 2 (.leaf 7450708837) (.leaf 7244789185))) (.branch 5 (.branch 4 (.leaf 7046871694) (.leaf 6856513177)) (.branch 6 (.leaf 6673302385) (.leaf 6496857196)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6326822100) (.leaf 6162865949)) (.branch 10 (.leaf 6004679929) (.leaf 5851975735))) (.branch 13 (.branch 12 (.leaf 5704483919) (.leaf 5561952404)) (.branch 14 (.leaf 5424145124) (.leaf 5290840800))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5161831817) (.branch 17 (.leaf 5036923208) (.leaf 4915931723))) (.branch 20 (.branch 19 (.leaf 4798684973) (.leaf 4685020659)) (.branch 21 (.leaf 4574785849) (.leaf 4467836329)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4364035997) (.leaf 4263256307)) (.branch 25 (.leaf 4165375765) (.leaf 4070279447))) (.branch 28 (.branch 27 (.leaf 3977858577) (.leaf 3888010113)) (.branch 29 (.leaf 3800636384) (.leaf 3715644745)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3632947254) (.branch 32 (.leaf 3552460382) (.leaf 3474104735))) (.branch 35 (.branch 34 (.leaf 3397804803) (.leaf 3323488721)) (.branch 36 (.leaf 3251088051) (.leaf 3180537576)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3111775110) (.leaf 3044741322)) (.branch 40 (.leaf 2979379568) (.leaf 2915635739))) (.branch 43 (.branch 42 (.leaf 2853458116) (.leaf 2792797235)) (.branch 44 (.leaf 2733605762) (.leaf 2675838376))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2619451655) (.branch 47 (.leaf 2564403981) (.leaf 2510655436))) (.branch 50 (.branch 49 (.leaf 2458167714) (.leaf 2406904039)) (.branch 51 (.leaf 2356829082) (.leaf 2307908888)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2260110806) (.leaf 2213403424)) (.branch 55 (.leaf 2167756505) (.leaf 2123140932))) (.branch 58 (.branch 57 (.leaf 2079528650) (.leaf 2036892617)) (.branch 59 (.leaf 1995206755) (.leaf 1954445905))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1914585780) (.branch 62 (.leaf 1875602933) (.leaf 1837474708))) (.branch 65 (.branch 64 (.leaf 1800179213) (.leaf 1763695281)) (.branch 66 (.leaf 1728002441) (.leaf 1693080882)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1658911431) (.leaf 1625475522)) (.branch 70 (.leaf 1592755172) (.leaf 1560732953))) (.branch 73 (.branch 72 (.leaf 1529391975) (.leaf 1498715857)) (.branch 74 (.leaf 1468688714) (.leaf 1439295130))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1410520144) (.branch 77 (.leaf 1382349231) (.leaf 1354768285))) (.branch 80 (.branch 79 (.leaf 1327763601) (.leaf 1301321866)) (.branch 81 (.leaf 1275430136) (.leaf 1250075829)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1225246708) (.leaf 1200930872)) (.branch 85 (.leaf 1177116740) (.leaf 1153793041))) (.branch 88 (.branch 87 (.leaf 1130948807) (.leaf 1108573357)) (.branch 89 (.leaf 1086656290) (.leaf 1065187475)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1044157042) (.branch 92 (.leaf 1023555375) (.leaf 1003373101))) (.branch 95 (.branch 94 (.leaf 983601083) (.leaf 964230413)) (.branch 96 (.leaf 945252406) (.leaf 926658590)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 908440701) (.leaf 890590679)) (.branch 100 (.leaf 873100655) (.leaf 855962955))) (.branch 103 (.branch 102 (.leaf 839170084) (.leaf 822714728)) (.branch 104 (.leaf 806589747) (.leaf 790788168))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 775303181) (.leaf 760128136)) (.branch 108 (.leaf 745256538) (.leaf 730682039))) (.branch 111 (.branch 110 (.leaf 716398439) (.leaf 702399681)) (.branch 112 (.leaf 688679844) (.leaf 675233142)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 662053919) (.leaf 649136647)) (.branch 116 (.leaf 636475922) (.leaf 624066460))) (.branch 119 (.branch 118 (.leaf 611903095) (.leaf 599980774)) (.branch 120 (.leaf 588294557) (.leaf 576839613)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1144).prefactor = (6352703929532359/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1144).cutoff/(generalMeanRows 1144).c)).2 =
    (24841415014619/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1144).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1144).q*(generalMeanRows 1144).c/2-2 = (307/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable081.value]
  have hcontinuation : (generalMeanRows 1144).q*(generalMeanRows 1144).cutoff/2-2 = (79/31:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable381.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1144).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1144).criticalRate j.val*(generalMeanRows 1144).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1144).c*(generalMeanRows 1144).criticalPoint j.val)).2-
      (generalMeanRows 1144).J/2-(generalMeanRows 1144).error (generalMeanGrid j.val)+
      (generalMeanRows 1144).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1144).c)).2-
      (generalMeanRows 1144).J/2-(generalMeanRows 1144).error 4 := by
  have he : (generalMeanRows 1144).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1144) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1144)
    (generalMeanRows_prefactorDomain 1144) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1144

/-! Kernel-checked entropy margins for general spectral rectangle 1145. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1145
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8190803008) (.branch 2 (.leaf 7970841080) (.leaf 7759473923))) (.branch 5 (.branch 4 (.leaf 7556214475) (.leaf 7360611587)) (.branch 6 (.leaf 7172246787) (.leaf 6990731403)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6815703984) (.leaf 6646827996)) (.branch 10 (.leaf 6483789737) (.leaf 6326296469))) (.branch 13 (.branch 12 (.leaf 6174074731) (.leaf 6026868803)) (.branch 14 (.leaf 5884439323) (.leaf 5746562029))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5613026607) (.branch 17 (.leaf 5483635652) (.leaf 5358203713))) (.branch 20 (.branch 19 (.leaf 5236556417) (.leaf 5118529675)) (.branch 21 (.leaf 5003968951) (.leaf 4892728587)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4784671187) (.leaf 4679667052)) (.branch 25 (.leaf 4577593652) (.leaf 4478335148))) (.branch 28 (.branch 27 (.leaf 4381781947) (.leaf 4287830288)) (.branch 29 (.leaf 4196381864) (.leaf 4107343471)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4020626680) (.branch 32 (.leaf 3936147539) (.leaf 3853826288))) (.branch 35 (.branch 34 (.leaf 3773587104) (.leaf 3695357854)) (.branch 36 (.leaf 3619069877) (.leaf 3544657769)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3472059193) (.leaf 3401214696)) (.branch 40 (.leaf 3332067539) (.leaf 3264563545))) (.branch 43 (.branch 42 (.leaf 3198650943) (.leaf 3134280240)) (.branch 44 (.leaf 3071404089) (.leaf 3009977167))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2949956067) (.branch 47 (.leaf 2891299192) (.leaf 2833966655))) (.branch 50 (.branch 49 (.leaf 2777920191) (.leaf 2723123067)) (.branch 51 (.leaf 2669540003) (.leaf 2617137099)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2565881757) (.leaf 2515742623)) (.branch 55 (.leaf 2466689517) (.leaf 2418693378))) (.branch 58 (.branch 57 (.leaf 2371726209) (.leaf 2325761023)) (.branch 59 (.leaf 2280771794) (.leaf 2236733414))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2193621646) (.branch 62 (.leaf 2151413083) (.leaf 2110085113))) (.branch 65 (.branch 64 (.leaf 2069615881) (.leaf 2029984251)) (.branch 66 (.leaf 1991169780) (.leaf 1953152682)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1915913802) (.leaf 1879434588)) (.branch 70 (.leaf 1843697065) (.leaf 1808683810))) (.branch 73 (.branch 72 (.leaf 1774377931) (.leaf 1740763041)) (.branch 74 (.leaf 1707823242) (.leaf 1675543101))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1643907635) (.branch 77 (.leaf 1612902292) (.leaf 1582512931))) (.branch 80 (.branch 79 (.leaf 1552725812) (.leaf 1523527576)) (.branch 81 (.leaf 1494905233) (.leaf 1466846148)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1439338025) (.leaf 1412368900)) (.branch 85 (.leaf 1385927126) (.leaf 1360001359))) (.branch 88 (.branch 87 (.leaf 1334580555) (.leaf 1309653950)) (.branch 89 (.leaf 1285211060) (.leaf 1261241664)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1237735798) (.branch 92 (.leaf 1214683748) (.leaf 1192076039))) (.branch 95 (.branch 94 (.leaf 1169903431) (.leaf 1148156906)) (.branch 96 (.leaf 1126827665) (.leaf 1105907122)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1085386895) (.leaf 1065258798)) (.branch 100 (.leaf 1045514840) (.leaf 1026147217))) (.branch 103 (.branch 102 (.leaf 1007148303) (.leaf 988510652)) (.branch 104 (.leaf 970226985) (.leaf 952290191))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 934693319) (.leaf 917429575)) (.branch 108 (.leaf 900492317) (.leaf 883875051))) (.branch 111 (.branch 110 (.leaf 867571428) (.leaf 851575236)) (.branch 112 (.leaf 835880402) (.leaf 820480985)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 805371173) (.leaf 790545278)) (.branch 116 (.leaf 775997738) (.leaf 761723107))) (.branch 119 (.branch 118 (.leaf 747716057) (.leaf 733971372)) (.branch 120 (.leaf 720483948) (.leaf 707248788)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1145).prefactor = (1624697486392061/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1145).cutoff/(generalMeanRows 1145).c)).2 =
    (513222110068057/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1145).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1145).q*(generalMeanRows 1145).c/2-2 = (289/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable093.value]
  have hcontinuation : (generalMeanRows 1145).q*(generalMeanRows 1145).cutoff/2-2 = (79/31:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable381.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1145).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1145).criticalRate j.val*(generalMeanRows 1145).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1145).c*(generalMeanRows 1145).criticalPoint j.val)).2-
      (generalMeanRows 1145).J/2-(generalMeanRows 1145).error (generalMeanGrid j.val)+
      (generalMeanRows 1145).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1145).c)).2-
      (generalMeanRows 1145).J/2-(generalMeanRows 1145).error 4 := by
  have he : (generalMeanRows 1145).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1145) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1145)
    (generalMeanRows_prefactorDomain 1145) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1145

/-! Kernel-checked entropy margins for general spectral rectangle 1146. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1146
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5759610046) (.branch 2 (.leaf 5570826975) (.leaf 5389998497))) (.branch 5 (.branch 4 (.leaf 5216675471) (.leaf 5050441486)) (.branch 6 (.leaf 4890909927) (.leaf 4737721367)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4590541214) (.leaf 4449057623)) (.branch 10 (.leaf 4312979599) (.leaf 4182035299))) (.branch 13 (.branch 12 (.leaf 4055970491) (.leaf 3934547168)) (.branch 14 (.leaf 3817542283) (.leaf 3704746603))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3595963666) (.branch 17 (.leaf 3491008834) (.leaf 3389708421))) (.branch 20 (.branch 19 (.leaf 3291898904) (.leaf 3197426196)) (.branch 21 (.leaf 3106144980) (.leaf 3017918099)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2932615997) (.leaf 2850116199)) (.branch 25 (.leaf 2770302842) (.leaf 2693066230))) (.branch 28 (.branch 27 (.leaf 2618302435) (.leaf 2545912924)) (.branch 29 (.leaf 2475804210) (.leaf 2407887535)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2342078574) (.branch 32 (.leaf 2278297161) (.leaf 2216467035))) (.branch 35 (.branch 34 (.leaf 2156515603) (.leaf 2098373721)) (.branch 36 (.leaf 2041975489) (.leaf 1987258063)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1934161477) (.leaf 1882628477)) (.branch 40 (.leaf 1832604371) (.leaf 1784036881))) (.branch 43 (.branch 42 (.leaf 1736876013) (.leaf 1691073929)) (.branch 44 (.leaf 1646584832) (.leaf 1603364856))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1561371964) (.branch 47 (.leaf 1520565851) (.leaf 1480907853))) (.branch 50 (.branch 49 (.leaf 1442360866) (.leaf 1404889266)) (.branch 51 (.leaf 1368458831) (.leaf 1333036676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1298591185) (.leaf 1265091950)) (.branch 55 (.leaf 1232509711) (.leaf 1200816304))) (.branch 58 (.branch 57 (.leaf 1169984609) (.leaf 1139988500)) (.branch 59 (.leaf 1110802801) (.leaf 1082403239))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1054766409) (.branch 62 (.leaf 1027869731) (.leaf 1001691415))) (.branch 65 (.branch 64 (.leaf 976210428) (.leaf 951406459)) (.branch 66 (.leaf 927259887) (.leaf 903751757)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 880863747) (.leaf 858578146)) (.branch 70 (.leaf 836877823) (.leaf 815746213))) (.branch 73 (.branch 72 (.leaf 795167283) (.leaf 775125520)) (.branch 74 (.leaf 755605906) (.leaf 736593900))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718075419) (.branch 77 (.leaf 700036822) (.leaf 682464891))) (.branch 80 (.branch 79 (.leaf 665346817) (.leaf 648670185)) (.branch 81 (.leaf 632422958) (.leaf 616593464)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 601170383) (.leaf 586142735)) (.branch 85 (.leaf 571499866) (.leaf 557231439))) (.branch 88 (.branch 87 (.leaf 543327422) (.leaf 529778075)) (.branch 89 (.leaf 516573945) (.leaf 503705852)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 491164882) (.branch 92 (.leaf 478942378) (.leaf 467029928))) (.branch 95 (.branch 94 (.leaf 455419363) (.leaf 444102746)) (.branch 96 (.leaf 433072361) (.leaf 422320713)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411840515) (.leaf 401624685)) (.branch 100 (.leaf 391666337) (.leaf 381958777))) (.branch 103 (.branch 102 (.leaf 372495494) (.leaf 363270160)) (.branch 104 (.leaf 354276617) (.leaf 345508877))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 336961116) (.leaf 328627668)) (.branch 108 (.leaf 320503020) (.leaf 312581809))) (.branch 111 (.branch 110 (.leaf 304858816) (.leaf 297328963)) (.branch 112 (.leaf 289987307) (.leaf 282829039)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 275849478) (.leaf 269044066)) (.branch 116 (.leaf 262408367) (.leaf 255938064))) (.branch 119 (.branch 118 (.leaf 249628952) (.leaf 243476939)) (.branch 120 (.leaf 237478039) (.leaf 231628372)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1146).prefactor = (1177311783168809/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1146).cutoff/(generalMeanRows 1146).c)).2 =
    (457503360759309/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1146).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1146).q*(generalMeanRows 1146).cutoff/2-2 = (1595/589:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable383.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1146).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1146).criticalRate j.val*(generalMeanRows 1146).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1146).c*(generalMeanRows 1146).criticalPoint j.val)).2-
      (generalMeanRows 1146).J/2-(generalMeanRows 1146).error (generalMeanGrid j.val)+
      (generalMeanRows 1146).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1146).c)).2-
      (generalMeanRows 1146).J/2-(generalMeanRows 1146).error 4 := by
  have he : (generalMeanRows 1146).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1146) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1146)
    (generalMeanRows_prefactorDomain 1146) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1146

/-! Kernel-checked entropy margins for general spectral rectangle 1147. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1147
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5714268850) (.branch 2 (.leaf 5520764053) (.leaf 5335541114))) (.branch 5 (.branch 4 (.leaf 5158132209) (.leaf 4988103463)) (.branch 6 (.leaf 4825051914) (.leaf 4668602811)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4518407193) (.leaf 4374139708)) (.branch 10 (.leaf 4235496670) (.leaf 4102194288))) (.branch 13 (.branch 12 (.leaf 3973967079) (.leaf 3850566427)) (.branch 14 (.leaf 3731759275) (.leaf 3617326941))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3507064034) (.branch 17 (.leaf 3400777475) (.leaf 3298285591))) (.branch 20 (.branch 19 (.leaf 3199417300) (.leaf 3104011353)) (.branch 21 (.leaf 3011915650) (.leaf 2922986601)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2837088547) (.leaf 2754093226)) (.branch 25 (.leaf 2673879275) (.leaf 2596331783))) (.branch 28 (.branch 27 (.leaf 2521341862) (.leaf 2448806267)) (.branch 29 (.leaf 2378627032) (.leaf 2310711141)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2244970218) (.branch 32 (.leaf 2181320246) (.leaf 2119681297))) (.branch 35 (.branch 34 (.leaf 2059977288) (.leaf 2002135755)) (.branch 36 (.leaf 1946087637) (.leaf 1891767079)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1839111249) (.leaf 1788060164)) (.branch 40 (.leaf 1738556530) (.leaf 1690545594))) (.branch 43 (.branch 42 (.leaf 1643975004) (.leaf 1598794674)) (.branch 44 (.leaf 1554956668) (.leaf 1512415081))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1471125934) (.branch 47 (.leaf 1431047071) (.leaf 1392138068))) (.branch 50 (.branch 49 (.leaf 1354360143) (.leaf 1317676073)) (.branch 51 (.leaf 1282050117) (.leaf 1247447940)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1213836547) (.leaf 1181184219)) (.branch 55 (.leaf 1149460446) (.leaf 1118635877))) (.branch 58 (.branch 57 (.leaf 1088682261) (.leaf 1059572398)) (.branch 59 (.leaf 1031280089) (.leaf 1003780092))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 977048079) (.branch 62 (.leaf 951060593) (.leaf 925795014))) (.branch 65 (.branch 64 (.leaf 901229516) (.leaf 877343041)) (.branch 66 (.leaf 854115258) (.leaf 831526538)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 809557923) (.leaf 788191094)) (.branch 70 (.leaf 767408354) (.leaf 747192593))) (.branch 73 (.branch 72 (.leaf 727527271) (.leaf 708396391)) (.branch 74 (.leaf 689784480) (.leaf 671676569))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 654058171) (.branch 77 (.leaf 636915264) (.leaf 620234273))) (.branch 80 (.branch 79 (.leaf 604002054) (.leaf 588205877)) (.branch 81 (.leaf 572833410) (.leaf 557872705)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 543312185) (.leaf 529140630)) (.branch 85 (.leaf 515347163) (.leaf 501921238))) (.branch 88 (.branch 87 (.leaf 488852632) (.leaf 476131428)) (.branch 89 (.leaf 463748008) (.leaf 451693042)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 439957477) (.branch 92 (.leaf 428532530) (.leaf 417409678))) (.branch 95 (.branch 94 (.leaf 406580646) (.leaf 396037403)) (.branch 96 (.leaf 385772154) (.leaf 375777328)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 366045575) (.leaf 356569757)) (.branch 100 (.leaf 347342941) (.leaf 338358393))) (.branch 103 (.branch 102 (.leaf 329609572) (.leaf 321090124)) (.branch 104 (.leaf 312793872) (.leaf 304714819))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 296847134) (.leaf 289185151)) (.branch 108 (.leaf 281723364) (.leaf 274456419))) (.branch 111 (.branch 110 (.leaf 267379115) (.leaf 260486394)) (.branch 112 (.leaf 253773338) (.leaf 247235167)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 240867232) (.leaf 234665014)) (.branch 116 (.leaf 228624116) (.leaf 222740266))) (.branch 119 (.branch 118 (.leaf 217009304) (.leaf 211427189)) (.branch 120 (.leaf 205989987) (.leaf 200693874)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1147).prefactor = (1218644785503627/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1147).cutoff/(generalMeanRows 1147).c)).2 =
    (88552215804421/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1147).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1147).q*(generalMeanRows 1147).cutoff/2-2 = (1595/589:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable383.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1147).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1147).criticalRate j.val*(generalMeanRows 1147).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1147).c*(generalMeanRows 1147).criticalPoint j.val)).2-
      (generalMeanRows 1147).J/2-(generalMeanRows 1147).error (generalMeanGrid j.val)+
      (generalMeanRows 1147).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1147).c)).2-
      (generalMeanRows 1147).J/2-(generalMeanRows 1147).error 4 := by
  have he : (generalMeanRows 1147).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1147) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1147)
    (generalMeanRows_prefactorDomain 1147) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1147

/-! Kernel-checked entropy margins for general spectral rectangle 1148. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1148
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6637278391) (.branch 2 (.leaf 6443479938) (.leaf 6257404178))) (.branch 5 (.branch 4 (.leaf 6078626164) (.leaf 5906751323)) (.branch 6 (.leaf 5741412763) (.leaf 5582268862)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5429001117) (.leaf 5281312217)) (.branch 10 (.leaf 5138924306) (.leaf 5001577420))) (.branch 13 (.branch 12 (.leaf 4869028076) (.leaf 4741047999)) (.branch 14 (.leaf 4617422953) (.leaf 4497951697))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4382445021) (.branch 17 (.leaf 4270724871) (.leaf 4162623550))) (.branch 20 (.branch 19 (.leaf 4057982987) (.leaf 3956654067)) (.branch 21 (.leaf 3858496012) (.leaf 3763375819)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3671167735) (.leaf 3581752783)) (.branch 25 (.leaf 3495018312) (.leaf 3410857595))) (.branch 28 (.branch 27 (.leaf 3329169446) (.leaf 3249857870)) (.branch 29 (.leaf 3172831744) (.leaf 3098004509)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3025293897) (.branch 32 (.leaf 2954621667) (.leaf 2885913367))) (.branch 35 (.branch 34 (.leaf 2819098108) (.leaf 2754108354)) (.branch 36 (.leaf 2690879729) (.leaf 2629350837)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2569463086) (.leaf 2511160537)) (.branch 40 (.leaf 2454389751) (.leaf 2399099653))) (.branch 43 (.branch 42 (.leaf 2345241400) (.leaf 2292768262)) (.branch 44 (.leaf 2241635508) (.leaf 2191800298))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2143221585) (.branch 47 (.leaf 2095860020) (.leaf 2049677862))) (.branch 50 (.branch 49 (.leaf 2004638901) (.leaf 1960708373)) (.branch 51 (.leaf 1917852893) (.leaf 1876040383)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1835240007) (.leaf 1795422111)) (.branch 55 (.leaf 1756558166) (.leaf 1718620714))) (.branch 58 (.branch 57 (.leaf 1681583314) (.leaf 1645420499)) (.branch 59 (.leaf 1610107723) (.leaf 1575621328))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1541938493) (.branch 62 (.leaf 1509037204) (.leaf 1476896212))) (.branch 65 (.branch 64 (.leaf 1445495004) (.leaf 1414813763)) (.branch 66 (.leaf 1384833347) (.leaf 1355535252)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1326901586) (.leaf 1298915048)) (.branch 70 (.leaf 1271558896) (.leaf 1244816927))) (.branch 73 (.branch 72 (.leaf 1218673457) (.leaf 1193113294)) (.branch 74 (.leaf 1168121725) (.leaf 1143684491))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1119787769) (.branch 77 (.leaf 1096418161) (.leaf 1073562671))) (.branch 80 (.branch 79 (.leaf 1051208691) (.leaf 1029343988)) (.branch 81 (.leaf 1007956689) (.leaf 987035265)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 966568524) (.leaf 946545590)) (.branch 85 (.leaf 926955901) (.leaf 907789190))) (.branch 88 (.branch 87 (.leaf 889035479) (.leaf 870685067)) (.branch 89 (.leaf 852728521) (.leaf 835156663)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 817960570) (.branch 92 (.leaf 801131556) (.leaf 784661167))) (.branch 95 (.branch 94 (.leaf 768541177) (.leaf 752763576)) (.branch 96 (.leaf 737320564) (.leaf 722204545)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 707408119) (.leaf 692924078)) (.branch 100 (.leaf 678745397) (.leaf 664865232))) (.branch 103 (.branch 102 (.leaf 651276911) (.leaf 637973928)) (.branch 104 (.leaf 624949944) (.leaf 612198773))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 599714386) (.leaf 587490900)) (.branch 108 (.leaf 575522577) (.leaf 563803819))) (.branch 111 (.branch 110 (.leaf 552329164) (.leaf 541093281)) (.branch 112 (.leaf 530090968) (.leaf 519317147)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 508766861) (.leaf 498435269)) (.branch 116 (.leaf 488317647) (.leaf 478409382))) (.branch 119 (.branch 118 (.leaf 468705965) (.leaf 459202997)) (.branch 120 (.leaf 449896179) (.leaf 440781312)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1148).prefactor = (5582582985475257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1148).cutoff/(generalMeanRows 1148).c)).2 =
    (437472590762467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1148).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1148).q*(generalMeanRows 1148).c/2-2 = (6387/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable379.value]
  have hcontinuation : (generalMeanRows 1148).q*(generalMeanRows 1148).cutoff/2-2 = (3088/1323:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable384.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1148).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1148).criticalRate j.val*(generalMeanRows 1148).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1148).c*(generalMeanRows 1148).criticalPoint j.val)).2-
      (generalMeanRows 1148).J/2-(generalMeanRows 1148).error (generalMeanGrid j.val)+
      (generalMeanRows 1148).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1148).c)).2-
      (generalMeanRows 1148).J/2-(generalMeanRows 1148).error 4 := by
  have he : (generalMeanRows 1148).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1148) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1148)
    (generalMeanRows_prefactorDomain 1148) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1148

/-! Kernel-checked entropy margins for general spectral rectangle 1149. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1149
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6687477093) (.branch 2 (.leaf 6484794993) (.leaf 6290297526))) (.branch 5 (.branch 4 (.leaf 6103535495) (.leaf 5924091668)) (.branch 6 (.leaf 5751577939) (.leaf 5585632810)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5425919122) (.leaf 5272122035)) (.branch 10 (.leaf 5123947204) (.leaf 4981119135))) (.branch 13 (.branch 12 (.leaf 4843379709) (.leaf 4710486830)) (.branch 14 (.leaf 4582213215) (.leaf 4458345284))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4338682152) (.branch 17 (.leaf 4223034708) (.leaf 4111224776))) (.branch 20 (.branch 19 (.leaf 4003084345) (.leaf 3898454864)) (.branch 21 (.leaf 3797186597) (.leaf 3699138021)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3604175286) (.leaf 3512171705)) (.branch 25 (.leaf 3423007290) (.leaf 3336568322))) (.branch 28 (.branch 27 (.leaf 3252746951) (.leaf 3171440829)) (.branch 29 (.leaf 3092552767) (.leaf 3015990422)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2941665996) (.branch 32 (.leaf 2869495972) (.leaf 2799400849))) (.branch 35 (.branch 34 (.leaf 2731304914) (.leaf 2665136019)) (.branch 36 (.leaf 2600825371) (.leaf 2538307349)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2477519316) (.leaf 2418401457)) (.branch 40 (.leaf 2360896623) (.leaf 2304950180))) (.branch 43 (.branch 42 (.leaf 2250509877) (.leaf 2197525716)) (.branch 44 (.leaf 2145949831) (.leaf 2095736375))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2046841415) (.branch 47 (.leaf 1999222835) (.leaf 1952840238))) (.branch 50 (.branch 49 (.leaf 1907654861) (.leaf 1863629493)) (.branch 51 (.leaf 1820728397) (.leaf 1778917234)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1738163001) (.leaf 1698433958)) (.branch 55 (.leaf 1659699575) (.leaf 1621930466))) (.branch 58 (.branch 57 (.leaf 1585098344) (.leaf 1549175962)) (.branch 59 (.leaf 1514137066) (.leaf 1479956355))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1446609431) (.branch 62 (.leaf 1414072758) (.leaf 1382323632))) (.branch 65 (.branch 64 (.leaf 1351340132) (.leaf 1321101096)) (.branch 66 (.leaf 1291586081) (.leaf 1262775337)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1234649773) (.leaf 1207190934)) (.branch 70 (.leaf 1180380968) (.leaf 1154202608))) (.branch 73 (.branch 72 (.leaf 1128639142) (.leaf 1103674395)) (.branch 74 (.leaf 1079292705) (.leaf 1055478900))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1032218285) (.branch 77 (.leaf 1009496617) (.leaf 987300093))) (.branch 80 (.branch 79 (.leaf 965615327) (.leaf 944429339)) (.branch 81 (.leaf 923729538) (.leaf 903503706)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 883739986) (.leaf 864426871)) (.branch 85 (.leaf 845553183) (.leaf 827108072))) (.branch 88 (.branch 87 (.leaf 809080995) (.leaf 791461712)) (.branch 89 (.leaf 774240270) (.leaf 757406997)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 740952489) (.branch 92 (.leaf 724867604) (.leaf 709143451))) (.branch 95 (.branch 94 (.leaf 693771383) (.leaf 678742987)) (.branch 96 (.leaf 664050078) (.leaf 649684690)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 635639071) (.leaf 621905674)) (.branch 100 (.leaf 608477152) (.leaf 595346351))) (.branch 103 (.branch 102 (.leaf 582506302) (.leaf 569950221)) (.branch 104 (.leaf 557671495) (.leaf 545663685))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 533920514) (.leaf 522435867)) (.branch 108 (.leaf 511203783) (.leaf 500218453))) (.branch 111 (.branch 110 (.leaf 489474212) (.leaf 478965537)) (.branch 112 (.leaf 468687046) (.leaf 458633486)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 448799737) (.leaf 439180804)) (.branch 116 (.leaf 429771815) (.leaf 420568017))) (.branch 119 (.branch 118 (.leaf 411564772) (.leaf 402757556)) (.branch 120 (.leaf 394141952) (.leaf 385713653)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1149).prefactor = (9173464940039/1562500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1149).cutoff/(generalMeanRows 1149).c)).2 =
    (21062800958661/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1149).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1149).q*(generalMeanRows 1149).cutoff/2-2 = (3088/1323:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable384.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1149).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1149).criticalRate j.val*(generalMeanRows 1149).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1149).c*(generalMeanRows 1149).criticalPoint j.val)).2-
      (generalMeanRows 1149).J/2-(generalMeanRows 1149).error (generalMeanGrid j.val)+
      (generalMeanRows 1149).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1149).c)).2-
      (generalMeanRows 1149).J/2-(generalMeanRows 1149).error 4 := by
  have he : (generalMeanRows 1149).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1149) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1149)
    (generalMeanRows_prefactorDomain 1149) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1149

/-! Kernel-checked entropy margins for general spectral rectangle 1150. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1150
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6345975021) (.branch 2 (.leaf 6163189400) (.leaf 5987675590))) (.branch 5 (.branch 4 (.leaf 5819028184) (.leaf 5656871174)) (.branch 6 (.leaf 5500855327) (.leaf 5350655842)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5205970250) (.leaf 5066516539)) (.branch 10 (.leaf 4932031459) (.leaf 4802269005))) (.branch 13 (.branch 12 (.leaf 4676999038) (.leaf 4556006040)) (.branch 14 (.leaf 4439087988) (.leaf 4326055324))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4216730026) (.branch 17 (.leaf 4110944754) (.leaf 4008542070))) (.branch 20 (.branch 19 (.leaf 3909373732) (.leaf 3813300040)) (.branch 21 (.leaf 3720189238) (.leaf 3629916966)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3542365757) (.leaf 3457424567)) (.branch 25 (.leaf 3374988354) (.leaf 3294957677))) (.branch 28 (.branch 27 (.leaf 3217238337) (.leaf 3141741031)) (.branch 29 (.leaf 3068381048) (.leaf 2997077976)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2927755433) (.branch 32 (.leaf 2860340820) (.leaf 2794765090))) (.branch 35 (.branch 34 (.leaf 2730962532) (.leaf 2668870571)) (.branch 36 (.leaf 2608429582) (.leaf 2549582721)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2492275756) (.leaf 2436456924)) (.branch 40 (.leaf 2382076784) (.leaf 2329088092))) (.branch 43 (.branch 42 (.leaf 2277445674) (.leaf 2227106311)) (.branch 44 (.leaf 2178028637) (.leaf 2130173033))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2083501535) (.branch 47 (.leaf 2037977746) (.leaf 1993566755))) (.branch 50 (.branch 49 (.leaf 1950235056) (.leaf 1907950479)) (.branch 51 (.leaf 1866682118) (.leaf 1826400272)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1787076377) (.leaf 1748682959)) (.branch 55 (.leaf 1711193573) (.leaf 1674582754))) (.branch 58 (.branch 57 (.leaf 1638825974) (.leaf 1603899592)) (.branch 59 (.leaf 1569780816) (.leaf 1536447662))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1503878916) (.branch 62 (.leaf 1472054099) (.leaf 1440953435))) (.branch 65 (.branch 64 (.leaf 1410557818) (.leaf 1380848781)) (.branch 66 (.leaf 1351808474) (.leaf 1323419629)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1295665540) (.leaf 1268530040)) (.branch 70 (.leaf 1241997473) (.leaf 1216052679))) (.branch 73 (.branch 72 (.leaf 1190680969) (.leaf 1165868108)) (.branch 74 (.leaf 1141600296) (.leaf 1117864152))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1094646695) (.branch 77 (.leaf 1071935331) (.leaf 1049717834))) (.branch 80 (.branch 79 (.leaf 1027982338) (.leaf 1006717319)) (.branch 81 (.leaf 985911583) (.leaf 965554254)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 945634763) (.leaf 926142837)) (.branch 85 (.leaf 907068486) (.leaf 888401995))) (.branch 88 (.branch 87 (.leaf 870133917) (.leaf 852255058)) (.branch 89 (.leaf 834756471) (.leaf 817629449)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 800865515) (.branch 92 (.leaf 784456416) (.leaf 768394112))) (.branch 95 (.branch 94 (.leaf 752670775) (.leaf 737278776)) (.branch 96 (.leaf 722210682) (.leaf 707459251)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 693017422) (.leaf 678878312)) (.branch 100 (.leaf 665035210) (.leaf 651481573))) (.branch 103 (.branch 102 (.leaf 638211018) (.leaf 625217320)) (.branch 104 (.leaf 612494406) (.leaf 600036350))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 587837370) (.leaf 575891823)) (.branch 108 (.leaf 564194202) (.leaf 552739130))) (.branch 111 (.branch 110 (.leaf 541521359) (.leaf 530535763)) (.branch 112 (.leaf 519777340) (.leaf 509241203)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 498922578) (.leaf 488816804)) (.branch 116 (.leaf 478919328) (.leaf 469225701))) (.branch 119 (.branch 118 (.leaf 459731576) (.leaf 450432707)) (.branch 120 (.leaf 441324945) (.leaf 432404232)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1150).prefactor = (2685870754734991/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1150).cutoff/(generalMeanRows 1150).c)).2 =
    (470046183342651/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1150).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1150).q*(generalMeanRows 1150).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1150).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1150).criticalRate j.val*(generalMeanRows 1150).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1150).c*(generalMeanRows 1150).criticalPoint j.val)).2-
      (generalMeanRows 1150).J/2-(generalMeanRows 1150).error (generalMeanGrid j.val)+
      (generalMeanRows 1150).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1150).c)).2-
      (generalMeanRows 1150).J/2-(generalMeanRows 1150).error 4 := by
  have he : (generalMeanRows 1150).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1150) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1150)
    (generalMeanRows_prefactorDomain 1150) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1150

/-! Kernel-checked entropy margins for general spectral rectangle 1151. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1151
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6539212835) (.branch 2 (.leaf 6348450641) (.leaf 6165311206))) (.branch 5 (.branch 4 (.leaf 5989370019) (.leaf 5820233306)) (.branch 6 (.leaf 5657535288) (.leaf 5500935726)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5350117739) (.leaf 5204785833)) (.branch 10 (.leaf 5064664141) (.leaf 4929494829))) (.branch 13 (.branch 12 (.leaf 4799036660) (.leaf 4673063693)) (.branch 14 (.leaf 4551364103) (.leaf 4433739110))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4320002003) (.branch 17 (.leaf 4209977250) (.leaf 4103499685))) (.branch 20 (.branch 19 (.leaf 4000413765) (.leaf 3900572891)) (.branch 21 (.leaf 3803838780) (.leaf 3710080895)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3619175915) (.leaf 3531007250)) (.branch 25 (.leaf 3445464595) (.leaf 3362443513))) (.branch 28 (.branch 27 (.leaf 3281845059) (.leaf 3203575420)) (.branch 29 (.leaf 3127545597) (.leaf 3053671094)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2981871643) (.branch 32 (.leaf 2912070943) (.leaf 2844196415))) (.branch 35 (.branch 34 (.leaf 2778178983) (.leaf 2713952859)) (.branch 36 (.leaf 2651455351) (.leaf 2590626683)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2531409825) (.leaf 2473750336)) (.branch 40 (.leaf 2417596214) (.leaf 2362897764))) (.branch 43 (.branch 42 (.leaf 2309607464) (.leaf 2257679849)) (.branch 44 (.leaf 2207071397) (.leaf 2157740424))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2109646987) (.branch 47 (.leaf 2062752788) (.leaf 2017021093))) (.branch 50 (.branch 49 (.leaf 1972416644) (.leaf 1928905590)) (.branch 51 (.leaf 1886455409) (.leaf 1845034846)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1804613847) (.leaf 1765163499)) (.branch 55 (.leaf 1726655975) (.leaf 1689064482))) (.branch 58 (.branch 57 (.leaf 1652363211) (.leaf 1616527290)) (.branch 59 (.leaf 1581532739) (.leaf 1547356430))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1513976047) (.branch 62 (.leaf 1481370048) (.leaf 1449517634))) (.branch 65 (.branch 64 (.leaf 1418398709) (.leaf 1387993855)) (.branch 66 (.leaf 1358284301) (.leaf 1329251892)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1300879066) (.leaf 1273148827)) (.branch 70 (.leaf 1246044723) (.leaf 1219550820))) (.branch 73 (.branch 72 (.leaf 1193651686) (.leaf 1168332365)) (.branch 74 (.leaf 1143578362) (.leaf 1119375622))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1095710516) (.branch 77 (.leaf 1072569819) (.leaf 1049940700))) (.branch 80 (.branch 79 (.leaf 1027810703) (.leaf 1006167738)) (.branch 81 (.leaf 985000059) (.leaf 964296259)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 944045254) (.leaf 924236273)) (.branch 85 (.leaf 904858844) (.leaf 885902787))) (.branch 88 (.branch 87 (.leaf 867358201) (.leaf 849215455)) (.branch 89 (.leaf 831465181) (.leaf 814098260)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 797105819) (.branch 92 (.leaf 780479221) (.leaf 764210054))) (.branch 95 (.branch 94 (.leaf 748290128) (.leaf 732711467)) (.branch 96 (.leaf 717466300) (.leaf 702547055)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 687946356) (.leaf 673657011)) (.branch 100 (.leaf 659672014) (.leaf 645984531))) (.branch 103 (.branch 102 (.leaf 632587901) (.leaf 619475627)) (.branch 104 (.leaf 606641374) (.leaf 594078962))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 581782363) (.leaf 569745696)) (.branch 108 (.leaf 557963221) (.leaf 546429338))) (.branch 111 (.branch 110 (.leaf 535138581) (.leaf 524085616)) (.branch 112 (.leaf 513265235) (.leaf 502672354)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 492302008) (.leaf 482149351)) (.branch 116 (.leaf 472209650) (.leaf 462478281))) (.branch 119 (.branch 118 (.leaf 452950730) (.leaf 443622586)) (.branch 120 (.leaf 434489542) (.leaf 425547389)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1151).prefactor = (2807643607896293/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1151).cutoff/(generalMeanRows 1151).c)).2 =
    (232349288508029/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1151).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1151).q*(generalMeanRows 1151).c/2-2 = (13/16:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable042.value]
  have hcontinuation : (generalMeanRows 1151).q*(generalMeanRows 1151).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1151).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1151).criticalRate j.val*(generalMeanRows 1151).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1151).c*(generalMeanRows 1151).criticalPoint j.val)).2-
      (generalMeanRows 1151).J/2-(generalMeanRows 1151).error (generalMeanGrid j.val)+
      (generalMeanRows 1151).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1151).c)).2-
      (generalMeanRows 1151).J/2-(generalMeanRows 1151).error 4 := by
  have he : (generalMeanRows 1151).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1151) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1151)
    (generalMeanRows_prefactorDomain 1151) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1151

/-! Kernel-checked entropy margins for general spectral rectangle 1152. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1152
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6642882490) (.branch 2 (.leaf 6444207791) (.leaf 6253544313))) (.branch 5 (.branch 4 (.leaf 6070446737) (.leaf 5894501883)) (.branch 6 (.leaf 5725325849) (.leaf 5562561449)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5405875931) (.leaf 5254958924)) (.branch 10 (.leaf 5109520594) (.leaf 4969289982))) (.branch 13 (.branch 12 (.leaf 4834013505) (.leaf 4703453595)) (.branch 14 (.leaf 4577387468) (.leaf 4455606003))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4337912724) (.branch 17 (.leaf 4224122871) (.leaf 4114062547))) (.branch 20 (.branch 19 (.leaf 4007567944) (.leaf 3904484634)) (.branch 21 (.leaf 3804666911) (.leaf 3707977194)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3614285476) (.leaf 3523468816)) (.branch 25 (.leaf 3435410870) (.leaf 3350001458))) (.branch 28 (.branch 27 (.leaf 3267136169) (.leaf 3186715986)) (.branch 29 (.leaf 3108646949) (.leaf 3032839837)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2959209872) (.branch 32 (.leaf 2887676452) (.leaf 2818162891))) (.branch 35 (.branch 34 (.leaf 2750596190) (.leaf 2684906815)) (.branch 36 (.leaf 2621028490) (.leaf 2558898016)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2498455084) (.leaf 2439642117)) (.branch 40 (.leaf 2382404112) (.leaf 2326688497))) (.branch 43 (.branch 42 (.leaf 2272444998) (.leaf 2219625510)) (.branch 44 (.leaf 2168183980) (.leaf 2118076300))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2069260197) (.branch 47 (.leaf 2021695144) (.leaf 1975342262))) (.branch 50 (.branch 49 (.leaf 1930164238) (.leaf 1886125246)) (.branch 51 (.leaf 1843190868) (.leaf 1801328029)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1760504922) (.leaf 1720690955)) (.branch 55 (.leaf 1681856684) (.leaf 1643973764))) (.branch 58 (.branch 57 (.leaf 1607014890) (.leaf 1570953754)) (.branch 59 (.leaf 1535764995) (.leaf 1501424156))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1467907643) (.branch 62 (.leaf 1435192683) (.leaf 1403257294))) (.branch 65 (.branch 64 (.leaf 1372080241) (.leaf 1341641010)) (.branch 66 (.leaf 1311919774) (.leaf 1282897362)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1254555234) (.leaf 1226875454)) (.branch 70 (.leaf 1199840661) (.leaf 1173434050))) (.branch 73 (.branch 72 (.leaf 1147639347) (.leaf 1122440787)) (.branch 74 (.leaf 1097823097) (.leaf 1073771469))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1050271552) (.branch 77 (.leaf 1027309425) (.leaf 1004871587))) (.branch 80 (.branch 79 (.leaf 982944937) (.leaf 961516760)) (.branch 81 (.leaf 940574714) (.leaf 920106815)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 900101424) (.leaf 880547234)) (.branch 85 (.leaf 861433260) (.leaf 842748826))) (.branch 88 (.branch 87 (.leaf 824483553) (.leaf 806627353)) (.branch 89 (.leaf 789170413) (.leaf 772103191)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 755416403) (.branch 92 (.leaf 739101019) (.leaf 723148248))) (.branch 95 (.branch 94 (.leaf 707549536) (.leaf 692296555)) (.branch 96 (.leaf 677381198) (.leaf 662795568)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 648531976) (.leaf 634582934)) (.branch 100 (.leaf 620941144) (.leaf 607599497))) (.branch 103 (.branch 102 (.leaf 594551065) (.leaf 581789098)) (.branch 104 (.leaf 569307014) (.leaf 557098399))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 545156997) (.leaf 533476711)) (.branch 108 (.leaf 522051595) (.leaf 510875847))) (.branch 111 (.branch 110 (.leaf 499943813) (.leaf 489249972)) (.branch 112 (.leaf 478788943) (.leaf 468555473)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 458544437) (.leaf 448750835)) (.branch 116 (.leaf 439169786) (.leaf 429796526))) (.branch 119 (.branch 118 (.leaf 420626406) (.leaf 411654888)) (.branch 120 (.leaf 402877541) (.leaf 394290038)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1152).prefactor = (2934937436979801/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1152).cutoff/(generalMeanRows 1152).c)).2 =
    (454088397904041/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1152).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1152).q*(generalMeanRows 1152).c/2-2 = (337/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable382.value]
  have hcontinuation : (generalMeanRows 1152).q*(generalMeanRows 1152).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable010.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1152).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1152).criticalRate j.val*(generalMeanRows 1152).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1152).c*(generalMeanRows 1152).criticalPoint j.val)).2-
      (generalMeanRows 1152).J/2-(generalMeanRows 1152).error (generalMeanGrid j.val)+
      (generalMeanRows 1152).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1152).c)).2-
      (generalMeanRows 1152).J/2-(generalMeanRows 1152).error 4 := by
  have he : (generalMeanRows 1152).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1152) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1152)
    (generalMeanRows_prefactorDomain 1152) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1152

/-! Kernel-checked entropy margins for general spectral rectangle 1153. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1153
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6325521752) (.branch 2 (.leaf 6145217456) (.leaf 5972065781))) (.branch 5 (.branch 4 (.leaf 5805663191) (.leaf 5645635874)) (.branch 6 (.leaf 5491637066) (.leaf 5343344662)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5200459078) (.leaf 5062701339)) (.branch 10 (.leaf 4929811350) (.leaf 4801546350))) (.branch 13 (.branch 12 (.leaf 4677679510) (.leaf 4557998661)) (.branch 14 (.leaf 4442305152) (.leaf 4330412801))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4222146947) (.branch 17 (.leaf 4117343585) (.leaf 4015848580))) (.branch 20 (.branch 19 (.leaf 3917516941) (.leaf 3822212163)) (.branch 21 (.leaf 3729805624) (.leaf 3640176026)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3553208890) (.leaf 3468796084)) (.branch 25 (.leaf 3386835391) (.leaf 3307230115))) (.branch 28 (.branch 27 (.leaf 3229888713) (.leaf 3154724451)) (.branch 29 (.leaf 3081655100) (.leaf 3010602640)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2941492993) (.branch 32 (.leaf 2874255777) (.leaf 2808824073))) (.branch 35 (.branch 34 (.leaf 2745134214) (.leaf 2683125584)) (.branch 36 (.leaf 2622740435) (.leaf 2563923715)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2506622909) (.leaf 2450787890)) (.branch 40 (.leaf 2396370781) (.leaf 2343325825))) (.branch 43 (.branch 42 (.leaf 2291609266) (.leaf 2241179233)) (.branch 44 (.leaf 2191995642) (.leaf 2144020091))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2097215770) (.branch 47 (.leaf 2051547378) (.leaf 2006981040))) (.branch 50 (.branch 49 (.leaf 1963484233) (.leaf 1921025712)) (.branch 51 (.leaf 1879575449) (.leaf 1839104570)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1799585292) (.leaf 1760990875)) (.branch 55 (.leaf 1723295564) (.leaf 1686474547))) (.branch 58 (.branch 57 (.leaf 1650503904) (.leaf 1615360570)) (.branch 59 (.leaf 1581022288) (.leaf 1547467578))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1514675695) (.branch 62 (.leaf 1482626600) (.leaf 1451300925))) (.branch 65 (.branch 64 (.leaf 1420679947) (.leaf 1390745554)) (.branch 66 (.leaf 1361480224) (.leaf 1332866995)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1304889444) (.leaf 1277531664)) (.branch 70 (.leaf 1250778240) (.leaf 1224614234))) (.branch 73 (.branch 72 (.leaf 1199025159) (.leaf 1173996966)) (.branch 74 (.leaf 1149516025) (.leaf 1125569108))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1102143374) (.branch 77 (.leaf 1079226354) (.leaf 1056805937))) (.branch 80 (.branch 79 (.leaf 1034870356) (.leaf 1013408177)) (.branch 81 (.leaf 992408285) (.leaf 971859873)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 951752432) (.leaf 932075737)) (.branch 85 (.leaf 912819844) (.leaf 893975072))) (.branch 88 (.branch 87 (.leaf 875531999) (.leaf 857481454)) (.branch 89 (.leaf 839814504) (.leaf 822522452)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 805596823) (.branch 92 (.leaf 789029362) (.leaf 772812025))) (.branch 95 (.branch 94 (.leaf 756936971) (.leaf 741396559)) (.branch 96 (.leaf 726183337) (.leaf 711290040)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 696709585) (.leaf 682435059)) (.branch 100 (.leaf 668459724) (.leaf 654777003))) (.branch 103 (.branch 102 (.leaf 641380479) (.leaf 628263890)) (.branch 104 (.leaf 615421126) (.leaf 602846221))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 590533353) (.leaf 578476836)) (.branch 108 (.leaf 566671119) (.leaf 555110782))) (.branch 111 (.branch 110 (.leaf 543790532) (.leaf 532705198)) (.branch 112 (.leaf 521849730) (.leaf 511219196)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 500808774) (.leaf 490613758)) (.branch 116 (.leaf 480629544) (.leaf 470851638))) (.branch 119 (.branch 118 (.leaf 461275646) (.leaf 451897273)) (.branch 120 (.leaf 442712321) (.leaf 433716689)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1153).prefactor = (2704125305523611/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1153).cutoff/(generalMeanRows 1153).c)).2 =
    (100549328930717/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1153).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1153).q*(generalMeanRows 1153).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1153).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1153).criticalRate j.val*(generalMeanRows 1153).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1153).c*(generalMeanRows 1153).criticalPoint j.val)).2-
      (generalMeanRows 1153).J/2-(generalMeanRows 1153).error (generalMeanGrid j.val)+
      (generalMeanRows 1153).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1153).c)).2-
      (generalMeanRows 1153).J/2-(generalMeanRows 1153).error 4 := by
  have he : (generalMeanRows 1153).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1153) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1153)
    (generalMeanRows_prefactorDomain 1153) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1153

/-! Kernel-checked entropy margins for general spectral rectangle 1154. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1154
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6487298790) (.branch 2 (.leaf 6300012571) (.leaf 6120189746))) (.branch 5 (.branch 4 (.leaf 5947409734) (.leaf 5781282882)) (.branch 6 (.leaf 5621447683) (.leaf 5467568287)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5319332287) (.leaf 5176448719)) (.branch 10 (.leaf 5038646278) (.leaf 4905671700))) (.branch 13 (.branch 12 (.leaf 4777288305) (.leaf 4653274684)) (.branch 14 (.leaf 4533423496) (.leaf 4417540389))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4305443010) (.branch 17 (.leaf 4196960107) (.leaf 4091930706))) (.branch 20 (.branch 19 (.leaf 3990203362) (.leaf 3891635475)) (.branch 21 (.leaf 3796092654) (.leaf 3703448148)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3613582310) (.leaf 3526382112)) (.branch 25 (.leaf 3441740693) (.leaf 3359556951))) (.branch 28 (.branch 27 (.leaf 3279735154) (.leaf 3202184594)) (.branch 29 (.leaf 3126819257) (.leaf 3053557524)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2982321891) (.branch 32 (.leaf 2913038709) (.leaf 2845637948))) (.branch 35 (.branch 34 (.leaf 2780052972) (.leaf 2716220331)) (.branch 36 (.leaf 2654079572) (.leaf 2593573059)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2534645807) (.leaf 2477245326)) (.branch 40 (.leaf 2421321479) (.leaf 2366826344))) (.branch 43 (.branch 42 (.leaf 2313714094) (.leaf 2261940874)) (.branch 44 (.leaf 2211464696) (.leaf 2162245332))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2114244223) (.branch 47 (.leaf 2067424387) (.leaf 2021750338))) (.branch 50 (.branch 49 (.leaf 1977188000) (.leaf 1933704644)) (.branch 51 (.leaf 1891268810) (.leaf 1849850247)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1809419852) (.leaf 1769949609)) (.branch 55 (.leaf 1731412541) (.leaf 1693782655))) (.branch 58 (.branch 57 (.leaf 1657034897) (.leaf 1621145107)) (.branch 59 (.leaf 1586089975) (.leaf 1551847004))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1518394471) (.branch 62 (.leaf 1485711393) (.leaf 1453777492))) (.branch 65 (.branch 64 (.leaf 1422573165) (.leaf 1392079453)) (.branch 66 (.leaf 1362278016) (.leaf 1333151102)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1304681526) (.leaf 1276852644)) (.branch 70 (.leaf 1249648331) (.leaf 1223052960))) (.branch 73 (.branch 72 (.leaf 1197051382) (.leaf 1171628905)) (.branch 74 (.leaf 1146771281) (.leaf 1122464681))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1098695685) (.branch 77 (.leaf 1075451264) (.leaf 1052718764))) (.branch 80 (.branch 79 (.leaf 1030485896) (.leaf 1008740719)) (.branch 81 (.leaf 987471626) (.leaf 966667336)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 946316882) (.leaf 926409596)) (.branch 85 (.leaf 906935101) (.leaf 887883302))) (.branch 88 (.branch 87 (.leaf 869244376) (.leaf 851008759)) (.branch 89 (.leaf 833167144) (.leaf 815710466)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 798629899) (.branch 92 (.leaf 781916845) (.leaf 765562927))) (.branch 95 (.branch 94 (.leaf 749559986) (.leaf 733900068)) (.branch 96 (.leaf 718575421) (.leaf 703578490)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 688901907) (.leaf 674538490)) (.branch 100 (.leaf 660481233) (.leaf 646723304))) (.branch 103 (.branch 102 (.leaf 633258038) (.leaf 620078934)) (.branch 104 (.leaf 607179647) (.leaf 594553987))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 582195914) (.leaf 570099531)) (.branch 108 (.leaf 558259083) (.leaf 546668950))) (.branch 111 (.branch 110 (.leaf 535323649) (.leaf 524217822)) (.branch 112 (.leaf 513346241) (.leaf 502703798)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 492285504) (.leaf 482086488)) (.branch 116 (.leaf 472101990) (.leaf 462327363))) (.branch 119 (.branch 118 (.leaf 452758063) (.leaf 443389653)) (.branch 120 (.leaf 434217798) (.leaf 425238260)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1154).prefactor = (5626720389793733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1154).cutoff/(generalMeanRows 1154).c)).2 =
    (497497288767443/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1154).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1154).q*(generalMeanRows 1154).c/2-2 = (3269/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable386.value]
  have hcontinuation : (generalMeanRows 1154).q*(generalMeanRows 1154).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1154).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1154).criticalRate j.val*(generalMeanRows 1154).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1154).c*(generalMeanRows 1154).criticalPoint j.val)).2-
      (generalMeanRows 1154).J/2-(generalMeanRows 1154).error (generalMeanGrid j.val)+
      (generalMeanRows 1154).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1154).c)).2-
      (generalMeanRows 1154).J/2-(generalMeanRows 1154).error 4 := by
  have he : (generalMeanRows 1154).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1154) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1154)
    (generalMeanRows_prefactorDomain 1154) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1154

/-! Kernel-checked entropy margins for general spectral rectangle 1155. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1155
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6653363550) (.branch 2 (.leaf 6458854083) (.leaf 6272131699))) (.branch 5 (.branch 4 (.leaf 6092758038) (.leaf 5920326919)) (.branch 6 (.leaf 5754461449) (.leaf 5594811439)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5441051096) (.leaf 5292876948)) (.branch 10 (.leaf 5150005987) (.leaf 5012173985))) (.branch 13 (.branch 12 (.leaf 4879133982) (.leaf 4750654917)) (.branch 14 (.leaf 4626520379) (.leaf 4506527488))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4390485857) (.branch 17 (.leaf 4278216665) (.leaf 4169551800))) (.branch 20 (.branch 19 (.leaf 4064333078) (.leaf 3962411529)) (.branch 21 (.leaf 3863646744) (.leaf 3767906274)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3675065076) (.leaf 3585005008)) (.branch 25 (.leaf 3497614362) (.leaf 3412787432))) (.branch 28 (.branch 27 (.leaf 3330424116) (.leaf 3250429554)) (.branch 29 (.leaf 3172713781) (.leaf 3097191421)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3023781392) (.branch 32 (.leaf 2952406638) (.leaf 2882993879))) (.branch 35 (.branch 34 (.leaf 2815473381) (.leaf 2749778739)) (.branch 36 (.leaf 2685846676) (.leaf 2623616860)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2563031729) (.leaf 2504036330)) (.branch 40 (.leaf 2446578168) (.leaf 2390607067))) (.branch 43 (.branch 42 (.leaf 2336075038) (.leaf 2282936158)) (.branch 44 (.leaf 2231146454) (.leaf 2180663801))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2131447814) (.branch 47 (.leaf 2083459763) (.leaf 2036662480))) (.branch 50 (.branch 49 (.leaf 1991020280) (.leaf 1946498883)) (.branch 51 (.leaf 1903065342) (.leaf 1860687975)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1819336303) (.leaf 1778980988)) (.branch 55 (.leaf 1739593780) (.leaf 1701147460))) (.branch 58 (.branch 57 (.leaf 1663615797) (.leaf 1626973493)) (.branch 59 (.leaf 1591196145) (.leaf 1556260203))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1522142927) (.branch 62 (.leaf 1488822357) (.leaf 1456277269))) (.branch 65 (.branch 64 (.leaf 1424487151) (.leaf 1393432166)) (.branch 66 (.leaf 1363093126) (.leaf 1333451464)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1304489204) (.leaf 1276188941)) (.branch 70 (.leaf 1248533815) (.leaf 1221507489))) (.branch 73 (.branch 72 (.leaf 1195094129) (.leaf 1169278379)) (.branch 74 (.leaf 1144045352) (.leaf 1119380600))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1095270107) (.branch 77 (.leaf 1071700265) (.leaf 1048657863))) (.branch 80 (.branch 79 (.leaf 1026130071) (.leaf 1004104426)) (.branch 81 (.leaf 982568819) (.leaf 961511479)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 940920968) (.leaf 920786161)) (.branch 85 (.leaf 901096241) (.leaf 881840685))) (.branch 88 (.branch 87 (.leaf 863009256) (.leaf 844591992)) (.branch 89 (.leaf 826579199) (.leaf 808961438)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 791729520) (.branch 92 (.leaf 774874497) (.leaf 758387655))) (.branch 95 (.branch 94 (.leaf 742260505) (.leaf 726484775)) (.branch 96 (.leaf 711052408) (.leaf 695955549)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 681186545) (.leaf 666737933)) (.branch 100 (.leaf 652602439) (.leaf 638772969))) (.branch 103 (.branch 102 (.leaf 625242606) (.leaf 612004605)) (.branch 104 (.leaf 599052384) (.leaf 586379525))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 573979764) (.leaf 561846992)) (.branch 108 (.leaf 549975245) (.leaf 538358703))) (.branch 111 (.branch 110 (.leaf 526991688) (.leaf 515868655)) (.branch 112 (.leaf 504984193) (.leaf 494333018)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 483909971) (.leaf 473710015)) (.branch 116 (.leaf 463728233) (.leaf 453959821))) (.branch 119 (.branch 118 (.leaf 444400087) (.leaf 435044450)) (.branch 120 (.leaf 425888434) (.leaf 416927668)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1155).prefactor = (5854015396448141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1155).cutoff/(generalMeanRows 1155).c)).2 =
    (492275344786291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1155).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1155).q*(generalMeanRows 1155).c/2-2 = (104/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable387.value]
  have hcontinuation : (generalMeanRows 1155).q*(generalMeanRows 1155).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1155).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1155).criticalRate j.val*(generalMeanRows 1155).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1155).c*(generalMeanRows 1155).criticalPoint j.val)).2-
      (generalMeanRows 1155).J/2-(generalMeanRows 1155).error (generalMeanGrid j.val)+
      (generalMeanRows 1155).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1155).c)).2-
      (generalMeanRows 1155).J/2-(generalMeanRows 1155).error 4 := by
  have he : (generalMeanRows 1155).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1155) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1155)
    (generalMeanRows_prefactorDomain 1155) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1155

/-! Kernel-checked entropy margins for general spectral rectangle 1156. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1156
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6727085986) (.branch 2 (.leaf 6525516500) (.leaf 6332093188))) (.branch 5 (.branch 4 (.leaf 6146358279) (.leaf 5967887503)) (.branch 6 (.leaf 5796287072) (.leaf 5631191007)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5472258726) (.leaf 5319172901)) (.branch 10 (.leaf 5171637515) (.leaf 5029376122))) (.branch 13 (.branch 12 (.leaf 4892130271) (.leaf 4759658078)) (.branch 14 (.leaf 4631732938) (.leaf 4508142348))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4388686842) (.branch 17 (.leaf 4273179015) (.leaf 4161442639))) (.branch 20 (.branch 19 (.leaf 4053311846) (.leaf 3948630390)) (.branch 21 (.leaf 3847250961) (.leaf 3749034567)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3653849952) (.leaf 3561573074)) (.branch 25 (.leaf 3472086616) (.leaf 3385279535))) (.branch 28 (.branch 27 (.leaf 3301046657) (.leaf 3219288285)) (.branch 29 (.leaf 3139909851) (.leaf 3062821589)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2987938232) (.branch 32 (.leaf 2915178730) (.leaf 2844465992))) (.branch 35 (.branch 34 (.leaf 2775726643) (.leaf 2708890799)) (.branch 36 (.leaf 2643891860) (.leaf 2580666316)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2519153563) (.leaf 2459295740)) (.branch 40 (.leaf 2401037568) (.leaf 2344326202))) (.branch 43 (.branch 42 (.leaf 2289111102) (.leaf 2235343896)) (.branch 44 (.leaf 2182978266) (.leaf 2131969838))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2082276072) (.branch 47 (.leaf 2033856170) (.leaf 1986670978))) (.branch 50 (.branch 49 (.leaf 1940682908) (.leaf 1895855852)) (.branch 51 (.leaf 1852155108) (.leaf 1809547310)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1768000359) (.leaf 1727483364)) (.branch 55 (.leaf 1687966580) (.leaf 1649421355))) (.branch 58 (.branch 57 (.leaf 1611820076) (.leaf 1575136121)) (.branch 59 (.leaf 1539343813) (.leaf 1504418376))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1470335893) (.branch 62 (.leaf 1437073270) (.leaf 1404608194))) (.branch 65 (.branch 64 (.leaf 1372919106) (.leaf 1341985162)) (.branch 66 (.leaf 1311786204) (.leaf 1282302732)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1253515874) (.leaf 1225407363)) (.branch 70 (.leaf 1197959509) (.leaf 1171155176))) (.branch 73 (.branch 72 (.leaf 1144977761) (.leaf 1119411173)) (.branch 74 (.leaf 1094439810) (.leaf 1070048544))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1046222698) (.branch 77 (.leaf 1022948034) (.leaf 1000210732))) (.branch 80 (.branch 79 (.leaf 977997376) (.leaf 956294942)) (.branch 81 (.leaf 935090778) (.leaf 914372594)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 894128450) (.leaf 874346742)) (.branch 85 (.leaf 855016189) (.leaf 836125826))) (.branch 88 (.branch 87 (.leaf 817664986) (.leaf 799623300)) (.branch 89 (.leaf 781990676) (.leaf 764757299)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 747913616) (.branch 92 (.leaf 731450330) (.leaf 715358390))) (.branch 95 (.branch 94 (.leaf 699628987) (.leaf 684253540)) (.branch 96 (.leaf 669223695) (.leaf 654531315)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 640168471) (.leaf 626127442)) (.branch 100 (.leaf 612400703) (.leaf 598980920))) (.branch 103 (.branch 102 (.leaf 585860946) (.leaf 573033816)) (.branch 104 (.leaf 560492739) (.leaf 548231094))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 536242427) (.leaf 524520442)) (.branch 108 (.leaf 513059000) (.leaf 501852116))) (.branch 111 (.branch 110 (.leaf 490893948) (.leaf 480178800)) (.branch 112 (.leaf 469701114) (.leaf 459455468)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449436571) (.leaf 439639261)) (.branch 116 (.leaf 430058499) (.leaf 420689367))) (.branch 119 (.branch 118 (.leaf 411527068) (.leaf 402566915)) (.branch 120 (.leaf 393804337) (.leaf 385234870)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1156).prefactor = (6090492131795469/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1156).cutoff/(generalMeanRows 1156).c)).2 =
    (481912557750743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1156).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1156).q*(generalMeanRows 1156).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1156).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1156).criticalRate j.val*(generalMeanRows 1156).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1156).c*(generalMeanRows 1156).criticalPoint j.val)).2-
      (generalMeanRows 1156).J/2-(generalMeanRows 1156).error (generalMeanGrid j.val)+
      (generalMeanRows 1156).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1156).c)).2-
      (generalMeanRows 1156).J/2-(generalMeanRows 1156).error 4 := by
  have he : (generalMeanRows 1156).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1156) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1156)
    (generalMeanRows_prefactorDomain 1156) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1156

/-! Kernel-checked entropy margins for general spectral rectangle 1157. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1157
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6899759302) (.branch 2 (.leaf 6690504291) (.leaf 6489746789))) (.branch 5 (.branch 4 (.leaf 6297009629) (.leaf 6111850499)) (.branch 6 (.leaf 5933858821) (.leaf 5762652953)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5597877697) (.leaf 5439202060)) (.branch 10 (.leaf 5286317239) (.leaf 5138934804))) (.branch 13 (.branch 12 (.leaf 4996785069) (.leaf 4859615599)) (.branch 14 (.leaf 4727189874) (.leaf 4599286062))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4475695915) (.branch 17 (.leaf 4356223751) (.leaf 4240685532))) (.branch 20 (.branch 19 (.leaf 4128908020) (.leaf 4020728004)) (.branch 21 (.leaf 3915991592) (.leaf 3814553558)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3716276747) (.leaf 3621031525)) (.branch 25 (.leaf 3528695273) (.leaf 3439151919))) (.branch 28 (.branch 27 (.leaf 3352291510) (.leaf 3268009810)) (.branch 29 (.leaf 3186207938) (.leaf 3106792022)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3029672888) (.branch 32 (.leaf 2954765767) (.leaf 2881990021))) (.branch 35 (.branch 34 (.leaf 2811268896) (.leaf 2742529284)) (.branch 36 (.leaf 2675701508) (.leaf 2610719120)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2547518711) (.leaf 2486039737)) (.branch 40 (.leaf 2426224354) (.leaf 2368017266))) (.branch 43 (.branch 42 (.leaf 2311365584) (.leaf 2256218689)) (.branch 44 (.leaf 2202528113) (.leaf 2150247417))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2099332086) (.branch 47 (.leaf 2049739426) (.leaf 2001428468))) (.branch 50 (.branch 49 (.leaf 1954359877) (.leaf 1908495873)) (.branch 51 (.leaf 1863800147) (.leaf 1820237788)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1777775216) (.leaf 1736380114)) (.branch 55 (.leaf 1696021368) (.leaf 1656669008))) (.branch 58 (.branch 57 (.leaf 1618294156) (.leaf 1580868969)) (.branch 59 (.leaf 1544366600) (.leaf 1508761142))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1474027593) (.branch 62 (.leaf 1440141812) (.leaf 1407080480))) (.branch 65 (.branch 64 (.leaf 1374821066) (.leaf 1343341790)) (.branch 66 (.leaf 1312621594) (.leaf 1282640109)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1253377627) (.leaf 1224815070)) (.branch 70 (.leaf 1196933972) (.leaf 1169716446))) (.branch 73 (.branch 72 (.leaf 1143145164) (.leaf 1117203336)) (.branch 74 (.leaf 1091874686) (.leaf 1067143434))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1042994277) (.branch 77 (.leaf 1019412369) (.leaf 996383305))) (.branch 80 (.branch 79 (.leaf 973893106) (.leaf 951928200)) (.branch 81 (.leaf 930475409) (.leaf 909521935)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 889055347) (.leaf 869063565)) (.branch 85 (.leaf 849534852) (.leaf 830457797))) (.branch 88 (.branch 87 (.leaf 811821310) (.leaf 793614604)) (.branch 89 (.leaf 775827192) (.leaf 758448871)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 741469717) (.branch 92 (.leaf 724880072) (.leaf 708670538))) (.branch 95 (.branch 94 (.leaf 692831969) (.leaf 677355461)) (.branch 96 (.leaf 662232345) (.leaf 647454180)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 633012747) (.leaf 618900039)) (.branch 100 (.leaf 605108259) (.leaf 591629808))) (.branch 103 (.branch 102 (.leaf 578457285) (.leaf 565583478)) (.branch 104 (.leaf 553001356) (.leaf 540704069))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 528684940) (.leaf 516937458)) (.branch 108 (.leaf 505455278) (.leaf 494232212))) (.branch 111 (.branch 110 (.leaf 483262225) (.leaf 472539434)) (.branch 112 (.leaf 462058101) (.leaf 451812629)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 441797557) (.leaf 432007560)) (.branch 116 (.leaf 422437444) (.leaf 413082138))) (.branch 119 (.branch 118 (.leaf 403936698) (.leaf 394996296)) (.branch 120 (.leaf 386256225) (.leaf 377711887)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1157).prefactor = (1584130374425089/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1157).cutoff/(generalMeanRows 1157).c)).2 =
    (119192789562581/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1157).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1157).q*(generalMeanRows 1157).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1157).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1157).criticalRate j.val*(generalMeanRows 1157).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1157).c*(generalMeanRows 1157).criticalPoint j.val)).2-
      (generalMeanRows 1157).J/2-(generalMeanRows 1157).error (generalMeanGrid j.val)+
      (generalMeanRows 1157).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1157).c)).2-
      (generalMeanRows 1157).J/2-(generalMeanRows 1157).error 4 := by
  have he : (generalMeanRows 1157).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1157) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1157)
    (generalMeanRows_prefactorDomain 1157) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1157

/-! Kernel-checked entropy margins for general spectral rectangle 1158. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1158
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7386275420) (.branch 2 (.leaf 7167645442) (.leaf 6957809279))) (.branch 5 (.branch 4 (.leaf 6756272359) (.leaf 6562576360)) (.branch 6 (.leaf 6376295950) (.leaf 6197035878)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6024428380) (.leaf 5858130841)) (.branch 10 (.leaf 5697823702) (.leaf 5543208573))) (.branch 13 (.branch 12 (.leaf 5394006521) (.leaf 5249956535)) (.branch 14 (.leaf 5110814120) (.leaf 4976350032))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4846349117) (.branch 17 (.leaf 4720609259) (.leaf 4598940423))) (.branch 20 (.branch 19 (.leaf 4481163768) (.leaf 4367110852)) (.branch 21 (.leaf 4256622887) (.leaf 4149550067)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4045750946) (.leaf 3945091866)) (.branch 25 (.leaf 3847446430) (.leaf 3752695020))) (.branch 28 (.branch 27 (.leaf 3660724346) (.leaf 3571427033)) (.branch 29 (.leaf 3484701241) (.leaf 3400450310)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3318582435) (.branch 32 (.leaf 3239010357) (.leaf 3161651089))) (.branch 35 (.branch 34 (.leaf 3086425649) (.leaf 3013258819)) (.branch 36 (.leaf 2942078922) (.leaf 2872817609)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2805409665) (.leaf 2739792826)) (.branch 40 (.leaf 2675907611) (.leaf 2613697164))) (.branch 43 (.branch 42 (.leaf 2553107103) (.leaf 2494085388)) (.branch 44 (.leaf 2436582186) (.leaf 2380549754))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2325942326) (.branch 47 (.leaf 2272716008) (.leaf 2220828677))) (.branch 50 (.branch 49 (.leaf 2170239891) (.leaf 2120910800)) (.branch 51 (.leaf 2072804065) (.leaf 2025883786)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1980115421) (.leaf 1935465728)) (.branch 55 (.leaf 1891902697) (.leaf 1849395490))) (.branch 58 (.branch 57 (.leaf 1807914385) (.leaf 1767430727)) (.branch 59 (.leaf 1727916871) (.leaf 1689346144))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1651692793) (.branch 62 (.leaf 1614931947) (.leaf 1579039577))) (.branch 65 (.branch 64 (.leaf 1543992458) (.leaf 1509768135)) (.branch 66 (.leaf 1476344891) (.leaf 1443701710)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1411818254) (.leaf 1380674830)) (.branch 70 (.leaf 1350252367) (.leaf 1320532387))) (.branch 73 (.branch 72 (.leaf 1291496984) (.leaf 1263128799)) (.branch 74 (.leaf 1235411000) (.leaf 1208327261))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1181861741) (.branch 77 (.leaf 1155999068) (.leaf 1130724320))) (.branch 80 (.branch 79 (.leaf 1106023009) (.leaf 1081881063)) (.branch 81 (.leaf 1058284811) (.leaf 1035220973)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1012676641) (.leaf 990639265)) (.branch 85 (.leaf 969096648) (.leaf 948036925))) (.branch 88 (.branch 87 (.leaf 927448557) (.leaf 907320317)) (.branch 89 (.leaf 887641282) (.leaf 868400822)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 849588589) (.branch 92 (.leaf 831194510) (.leaf 813208777))) (.branch 95 (.branch 94 (.leaf 795621839) (.leaf 778424391)) (.branch 96 (.leaf 761607372) (.leaf 745161952)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 729079528) (.leaf 713351716)) (.branch 100 (.leaf 697970345) (.leaf 682927448))) (.branch 103 (.branch 102 (.leaf 668215262) (.leaf 653826213)) (.branch 104 (.leaf 639752920) (.leaf 625988182))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 612524977) (.leaf 599356455)) (.branch 108 (.leaf 586475933) (.leaf 573876893))) (.branch 111 (.branch 110 (.leaf 561552974) (.leaf 549497968)) (.branch 112 (.leaf 537705819) (.leaf 526170614)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 514886584) (.leaf 503848096)) (.branch 116 (.leaf 493049653) (.leaf 482485887))) (.branch 119 (.branch 118 (.leaf 472151557) (.leaf 462041545)) (.branch 120 (.leaf 452150857) (.leaf 442474612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1158).prefactor = (824061172355997/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1158).cutoff/(generalMeanRows 1158).c)).2 =
    (243540263954593/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1158).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1158).q*(generalMeanRows 1158).c/2-2 = (3387/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable388.value]
  have hcontinuation : (generalMeanRows 1158).q*(generalMeanRows 1158).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1158).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1158).criticalRate j.val*(generalMeanRows 1158).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1158).c*(generalMeanRows 1158).criticalPoint j.val)).2-
      (generalMeanRows 1158).J/2-(generalMeanRows 1158).error (generalMeanGrid j.val)+
      (generalMeanRows 1158).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1158).c)).2-
      (generalMeanRows 1158).J/2-(generalMeanRows 1158).error 4 := by
  have he : (generalMeanRows 1158).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1158) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1158)
    (generalMeanRows_prefactorDomain 1158) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1158

/-! Kernel-checked entropy margins for general spectral rectangle 1159. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1159
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8126421757) (.branch 2 (.leaf 7900731261) (.leaf 7683915094))) (.branch 5 (.branch 4 (.leaf 7475471248) (.leaf 7274934822)) (.branch 6 (.leaf 7081874672) (.leaf 6895890424)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6716609808) (.leaf 6543686259)) (.branch 10 (.leaf 6376796769) (.leaf 6215639941))) (.branch 13 (.branch 12 (.leaf 6059934246) (.leaf 5909416432)) (.branch 14 (.leaf 5763840094) (.leaf 5622974365))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5486602733) (.branch 17 (.leaf 5354521962) (.leaf 5226541102))) (.branch 20 (.branch 19 (.leaf 5102480590) (.leaf 4982171428)) (.branch 21 (.leaf 4865454424) (.leaf 4752179500)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4642205059) (.leaf 4535397395)) (.branch 25 (.leaf 4431630156) (.leaf 4330783850))) (.branch 28 (.branch 27 (.leaf 4232745385) (.leaf 4137407647)) (.branch 29 (.leaf 4044669107) (.leaf 3954433465)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3866609313) (.branch 32 (.leaf 3781109823) (.leaf 3697852464))) (.branch 35 (.branch 34 (.leaf 3616758733) (.leaf 3537753908)) (.branch 36 (.leaf 3460766820) (.leaf 3385729637)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3312577667) (.leaf 3241249172)) (.branch 40 (.leaf 3171685195) (.leaf 3103829403))) (.branch 43 (.branch 42 (.leaf 3037627930) (.leaf 2973029247)) (.branch 44 (.leaf 2909984021) (.leaf 2848445002))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2788366902) (.branch 47 (.leaf 2729706293) (.leaf 2672421504))) (.branch 50 (.branch 49 (.leaf 2616472532) (.leaf 2561820947)) (.branch 51 (.leaf 2508429819) (.leaf 2456263634)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2405288223) (.leaf 2355470699)) (.branch 55 (.leaf 2306779385) (.leaf 2259183764))) (.branch 58 (.branch 57 (.leaf 2212654414) (.leaf 2167162961)) (.branch 59 (.leaf 2122682024) (.leaf 2079185174))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2036646886) (.branch 62 (.leaf 1995042498) (.leaf 1954348172))) (.branch 65 (.branch 64 (.leaf 1914540857) (.leaf 1875598254)) (.branch 66 (.leaf 1837498783) (.leaf 1800221552)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1763746326) (.leaf 1728053503)) (.branch 70 (.leaf 1693124083) (.leaf 1658939645))) (.branch 73 (.branch 72 (.leaf 1625482325) (.leaf 1592734791)) (.branch 74 (.leaf 1560680221) (.leaf 1529302288))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1498585134) (.branch 77 (.leaf 1468513357) (.leaf 1439071993))) (.branch 80 (.branch 79 (.leaf 1410246495) (.leaf 1382022724)) (.branch 81 (.leaf 1354386930) (.leaf 1327325739)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1300826139) (.leaf 1274875469)) (.branch 85 (.leaf 1249461402) (.leaf 1224571941))) (.branch 88 (.branch 87 (.leaf 1200195401) (.leaf 1176320400)) (.branch 89 (.leaf 1152935853) (.leaf 1130030955)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1107595180) (.branch 92 (.leaf 1085618264) (.leaf 1064090202))) (.branch 95 (.branch 94 (.leaf 1043001239) (.leaf 1022341861)) (.branch 96 (.leaf 1002102786) (.leaf 982274960)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 962849550) (.leaf 943817935)) (.branch 100 (.leaf 925171701) (.leaf 906902634))) (.branch 103 (.branch 102 (.leaf 889002717) (.leaf 871464121)) (.branch 104 (.leaf 854279200) (.leaf 837440487))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 820940691) (.leaf 804772686)) (.branch 108 (.leaf 788929513) (.leaf 773404372))) (.branch 111 (.branch 110 (.leaf 758190617) (.leaf 743281754)) (.branch 112 (.leaf 728671436) (.leaf 714353458)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 700321758) (.leaf 686570404)) (.branch 116 (.leaf 673093601) (.leaf 659885681))) (.branch 119 (.branch 118 (.leaf 646941101) (.leaf 634254441)) (.branch 120 (.leaf 621820400) (.leaf 609633792)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1159).prefactor = (6751006940367103/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1159).cutoff/(generalMeanRows 1159).c)).2 =
    (128332188496031/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1159).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1159).q*(generalMeanRows 1159).cutoff/2-2 = (3152/1197:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable385.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1159).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1159).criticalRate j.val*(generalMeanRows 1159).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1159).c*(generalMeanRows 1159).criticalPoint j.val)).2-
      (generalMeanRows 1159).J/2-(generalMeanRows 1159).error (generalMeanGrid j.val)+
      (generalMeanRows 1159).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1159).c)).2-
      (generalMeanRows 1159).J/2-(generalMeanRows 1159).error 4 := by
  have he : (generalMeanRows 1159).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1159) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1159)
    (generalMeanRows_prefactorDomain 1159) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1159

/-! Kernel-checked entropy margins for general spectral rectangle 1160. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1160
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5950846350) (.branch 2 (.leaf 5758885474) (.leaf 5574933691))) (.branch 5 (.branch 4 (.leaf 5398537791) (.leaf 5229277882)) (.branch 6 (.leaf 5066764387) (.leaf 4910635361)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4760554094) (.leaf 4616206957)) (.branch 10 (.leaf 4477301473) (.leaf 4343564571))) (.branch 13 (.branch 12 (.leaf 4214741015) (.leaf 4090591984)) (.branch 14 (.leaf 3970893776) (.leaf 3855436646))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3744023737) (.branch 17 (.leaf 3636470111) (.leaf 3532601867))) (.branch 20 (.branch 19 (.leaf 3432255334) (.leaf 3335276329)) (.branch 21 (.leaf 3241519484) (.leaf 3150847625)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3063131204) (.leaf 2978247772)) (.branch 25 (.leaf 2896081502) (.leaf 2816522744))) (.branch 28 (.branch 27 (.leaf 2739467616) (.leaf 2664817625)) (.branch 29 (.leaf 2592479324) (.leaf 2522363985)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2454387303) (.branch 32 (.leaf 2388469118) (.leaf 2324533163))) (.branch 35 (.branch 34 (.leaf 2262506825) (.leaf 2202320922)) (.branch 36 (.leaf 2143909502) (.leaf 2087209652)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2032161319) (.leaf 1978707149)) (.branch 40 (.leaf 1926792330) (.leaf 1876364449))) (.branch 43 (.branch 42 (.leaf 1827373362) (.leaf 1779771064)) (.branch 44 (.leaf 1733511577) (.leaf 1688550840))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1644846606) (.branch 47 (.leaf 1602358348) (.leaf 1561047168))) (.branch 50 (.branch 49 (.leaf 1520875715) (.leaf 1481808106)) (.branch 51 (.leaf 1443809853) (.leaf 1406847792)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1370890021) (.leaf 1335905837)) (.branch 55 (.leaf 1301865677) (.leaf 1268741067))) (.branch 58 (.branch 57 (.leaf 1236504573) (.leaf 1205129744)) (.branch 59 (.leaf 1174591079) (.leaf 1144863975))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1115924689) (.branch 62 (.leaf 1087750305) (.leaf 1060318689))) (.branch 65 (.branch 64 (.leaf 1033608466) (.leaf 1007598976)) (.branch 66 (.leaf 982270254) (.leaf 957602995)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 933578529) (.leaf 910178793)) (.branch 70 (.leaf 887386311) (.leaf 865184165))) (.branch 73 (.branch 72 (.leaf 843555976) (.leaf 822485885)) (.branch 74 (.leaf 801958527) (.leaf 781959018))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 762472934) (.branch 77 (.leaf 743486292) (.leaf 724985539))) (.branch 80 (.branch 79 (.leaf 706957531) (.leaf 689389519)) (.branch 81 (.leaf 672269137) (.leaf 655584389)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 639323631) (.leaf 623475563)) (.branch 85 (.leaf 608029216) (.leaf 592973939))) (.branch 88 (.branch 87 (.leaf 578299392) (.leaf 563995530)) (.branch 89 (.leaf 550052599) (.leaf 536461121)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 523211888) (.branch 92 (.leaf 510295954) (.leaf 497704623))) (.branch 95 (.branch 94 (.leaf 485429443) (.leaf 473462199)) (.branch 96 (.leaf 461794905) (.leaf 450419794)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 439329316) (.leaf 428516127)) (.branch 100 (.leaf 417973085) (.leaf 407693244))) (.branch 103 (.branch 102 (.leaf 397669844) (.leaf 387896313)) (.branch 104 (.leaf 378366253) (.leaf 369073440))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360011819) (.leaf 351175494)) (.branch 108 (.leaf 342558731) (.leaf 334155944))) (.branch 111 (.branch 110 (.leaf 325961700) (.leaf 317970708)) (.branch 112 (.leaf 310177817) (.leaf 302578014)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 295166415) (.leaf 287938268)) (.branch 116 (.leaf 280888943) (.leaf 274013932))) (.branch 119 (.branch 118 (.leaf 267308846) (.leaf 260769408)) (.branch 120 (.leaf 254391455) (.leaf 248170931)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1160).prefactor = (150736994121601/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1160).cutoff/(generalMeanRows 1160).c)).2 =
    (480827958945943/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1160).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1160).q*(generalMeanRows 1160).cutoff/2-2 = (1592/567:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable389.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1160).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1160).criticalRate j.val*(generalMeanRows 1160).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1160).c*(generalMeanRows 1160).criticalPoint j.val)).2-
      (generalMeanRows 1160).J/2-(generalMeanRows 1160).error (generalMeanGrid j.val)+
      (generalMeanRows 1160).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1160).c)).2-
      (generalMeanRows 1160).J/2-(generalMeanRows 1160).error 4 := by
  have he : (generalMeanRows 1160).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1160) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1160)
    (generalMeanRows_prefactorDomain 1160) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1160

/-! Kernel-checked entropy margins for general spectral rectangle 1161. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1161
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5912155642) (.branch 2 (.leaf 5715099662) (.leaf 5526396112))) (.branch 5 (.branch 4 (.leaf 5345572251) (.leaf 5172189937)) (.branch 6 (.leaf 5005842518) (.leaf 4846152051)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4692766824) (.leaf 4545359121)) (.branch 10 (.leaf 4403623223) (.leaf 4267273604))) (.branch 13 (.branch 12 (.leaf 4136043296) (.leaf 4009682419)) (.branch 14 (.leaf 3887956845) (.leaf 3770646982))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3657546670) (.branch 17 (.leaf 3548462179) (.leaf 3443211290))) (.branch 20 (.branch 19 (.leaf 3341622456) (.leaf 3243534038)) (.branch 21 (.leaf 3148793601) (.leaf 3057257270)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2968789139) (.leaf 2883260730)) (.branch 25 (.leaf 2800550488) (.leaf 2720543323))) (.branch 28 (.branch 27 (.leaf 2643130183) (.leaf 2568207665)) (.branch 29 (.leaf 2495677649) (.leaf 2425446964)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2357427079) (.branch 32 (.leaf 2291533811) (.leaf 2227687064))) (.branch 35 (.branch 34 (.leaf 2165810580) (.leaf 2105831705)) (.branch 36 (.leaf 2047681182) (.leaf 1991292947)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1936603947) (.leaf 1883553968)) (.branch 40 (.leaf 1832085473) (.leaf 1782143452))) (.branch 43 (.branch 42 (.leaf 1733675286) (.leaf 1686630611)) (.branch 44 (.leaf 1640961200) (.leaf 1596620848))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1553565263) (.branch 47 (.leaf 1511751971) (.leaf 1471140217))) (.branch 50 (.branch 49 (.leaf 1431690879) (.leaf 1393366388)) (.branch 51 (.leaf 1356130648) (.leaf 1319948962)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1284787968) (.leaf 1250615571)) (.branch 55 (.leaf 1217400885) (.leaf 1185114173))) (.branch 58 (.branch 57 (.leaf 1153726798) (.leaf 1123211166)) (.branch 59 (.leaf 1093540686) (.leaf 1064689719))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1036633536) (.branch 62 (.leaf 1009348283) (.leaf 982810934))) (.branch 65 (.branch 64 (.leaf 956999266) (.leaf 931891815)) (.branch 66 (.leaf 907467850) (.leaf 883707340)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 860590926) (.leaf 838099891)) (.branch 70 (.leaf 816216140) (.leaf 794922167))) (.branch 73 (.branch 72 (.leaf 774201038) (.leaf 754036367)) (.branch 74 (.leaf 734412292) (.leaf 715313458))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 696724997) (.branch 77 (.leaf 678632507) (.leaf 661022040))) (.branch 80 (.branch 79 (.leaf 643880078) (.leaf 627193525)) (.branch 81 (.leaf 610949685) (.leaf 595136251)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 579741290) (.leaf 564753231)) (.branch 85 (.leaf 550160852) (.leaf 535953265))) (.branch 88 (.branch 87 (.leaf 522119908) (.leaf 508650532)) (.branch 89 (.leaf 495535192) (.leaf 482764234)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 470328287) (.branch 92 (.leaf 458218255) (.leaf 446425304))) (.branch 95 (.branch 94 (.leaf 434940857) (.leaf 423756585)) (.branch 96 (.leaf 412864395) (.leaf 402256430)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 391925054) (.leaf 381862849)) (.branch 100 (.leaf 372062608) (.leaf 362517326))) (.branch 103 (.branch 102 (.leaf 353220197) (.leaf 344164604)) (.branch 104 (.leaf 335344118) (.leaf 326752488))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 318383636) (.leaf 310231654)) (.branch 108 (.leaf 302290799) (.leaf 294555484))) (.branch 111 (.branch 110 (.leaf 287020277) (.leaf 279679897)) (.branch 112 (.leaf 272529205) (.leaf 265563206)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 258777039) (.leaf 252165976)) (.branch 116 (.leaf 245725419) (.leaf 239450894))) (.branch 119 (.branch 118 (.leaf 233338047) (.leaf 227382645)) (.branch 120 (.leaf 221580566) (.leaf 215927801)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1161).prefactor = (3124379102950083/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1161).cutoff/(generalMeanRows 1161).c)).2 =
    (46629985838303/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1161).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1161).q*(generalMeanRows 1161).cutoff/2-2 = (1592/567:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable389.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1161).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1161).criticalRate j.val*(generalMeanRows 1161).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1161).c*(generalMeanRows 1161).criticalPoint j.val)).2-
      (generalMeanRows 1161).J/2-(generalMeanRows 1161).error (generalMeanGrid j.val)+
      (generalMeanRows 1161).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1161).c)).2-
      (generalMeanRows 1161).J/2-(generalMeanRows 1161).error 4 := by
  have he : (generalMeanRows 1161).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1161) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1161)
    (generalMeanRows_prefactorDomain 1161) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1161

/-! Kernel-checked entropy margins for general spectral rectangle 1162. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1162
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6367701250) (.branch 2 (.leaf 6164574804) (.leaf 5969879319))) (.branch 5 (.branch 4 (.leaf 5783137659) (.leaf 5603907814)) (.branch 6 (.leaf 5431779740) (.leaf 5266372522)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5107331844) (.leaf 4954327724)) (.branch 10 (.leaf 4807052466) (.leaf 4665218827))) (.branch 13 (.branch 12 (.leaf 4528558357) (.leaf 4396819897)) (.branch 14 (.leaf 4269768220) (.leaf 4147182794))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4028856665) (.branch 17 (.leaf 3914595427) (.leaf 3804216296))) (.branch 20 (.branch 19 (.leaf 3697547258) (.leaf 3594426286)) (.branch 21 (.leaf 3494700631) (.leaf 3398226165)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3304866784) (.leaf 3214493855)) (.branch 25 (.leaf 3126985707) (.leaf 3042227167))) (.branch 28 (.branch 27 (.leaf 2960109127) (.leaf 2880528146)) (.branch 29 (.leaf 2803386084) (.leaf 2728589764)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2656050657) (.branch 32 (.leaf 2585684588) (.leaf 2517411473))) (.branch 35 (.branch 34 (.leaf 2451155064) (.leaf 2386842720)) (.branch 36 (.leaf 2324405187) (.leaf 2263776407)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2204893321) (.leaf 2147695701)) (.branch 40 (.leaf 2092125992) (.leaf 2038129152))) (.branch 43 (.branch 42 (.leaf 1985652520) (.leaf 1934645682)) (.branch 44 (.leaf 1885060346) (.leaf 1836850233))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1789970964) (.branch 47 (.leaf 1744379965) (.leaf 1700036368))) (.branch 50 (.branch 49 (.leaf 1656900930) (.leaf 1614935943)) (.branch 51 (.leaf 1574105161) (.leaf 1534373728)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1495708108) (.leaf 1458076021)) (.branch 55 (.leaf 1421446383) (.leaf 1385789251))) (.branch 58 (.branch 57 (.leaf 1351075766) (.leaf 1317278107)) (.branch 59 (.leaf 1284369440) (.leaf 1252323876))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1221116427) (.branch 62 (.leaf 1190722967) (.leaf 1161120192))) (.branch 65 (.branch 64 (.leaf 1132285591) (.leaf 1104197405)) (.branch 66 (.leaf 1076834598) (.leaf 1050176827)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1024204415) (.leaf 998898320)) (.branch 70 (.leaf 974240114) (.leaf 950211953))) (.branch 73 (.branch 72 (.leaf 926796559) (.leaf 903977197)) (.branch 74 (.leaf 881737650) (.leaf 860062205))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 838935630) (.branch 77 (.leaf 818343156) (.leaf 798270463))) (.branch 80 (.branch 79 (.leaf 778703660) (.leaf 759629272)) (.branch 81 (.leaf 741034223) (.leaf 722905824)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705231758) (.leaf 688000065)) (.branch 85 (.leaf 671199135) (.leaf 654817691))) (.branch 88 (.branch 87 (.leaf 638844780) (.leaf 623269761)) (.branch 89 (.leaf 608082295) (.leaf 593272337)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 578830122) (.branch 92 (.leaf 564746161) (.leaf 551011227))) (.branch 95 (.branch 94 (.leaf 537616350) (.leaf 524552809)) (.branch 96 (.leaf 511812121) (.leaf 499386038)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 487266534) (.leaf 475445804)) (.branch 100 (.leaf 463916254) (.leaf 452670495))) (.branch 103 (.branch 102 (.leaf 441701337) (.leaf 431001782)) (.branch 104 (.leaf 420565020) (.leaf 410384423))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 400453540) (.leaf 390766087)) (.branch 108 (.leaf 381315952) (.leaf 372097179))) (.branch 111 (.branch 110 (.leaf 363103972) (.leaf 354330685)) (.branch 112 (.leaf 345771820) (.leaf 337422024)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 329276081) (.leaf 321328913)) (.branch 116 (.leaf 313575572) (.leaf 306011238))) (.branch 119 (.branch 118 (.leaf 298631217) (.leaf 291430933)) (.branch 120 (.leaf 284405931) (.leaf 277551867)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1162).prefactor = (6361370039443201/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1162).cutoff/(generalMeanRows 1162).c)).2 =
    (121429486060033/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1162).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1162).q*(generalMeanRows 1162).cutoff/2-2 = (1592/567:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable389.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1162).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1162).criticalRate j.val*(generalMeanRows 1162).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1162).c*(generalMeanRows 1162).criticalPoint j.val)).2-
      (generalMeanRows 1162).J/2-(generalMeanRows 1162).error (generalMeanGrid j.val)+
      (generalMeanRows 1162).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1162).c)).2-
      (generalMeanRows 1162).J/2-(generalMeanRows 1162).error 4 := by
  have he : (generalMeanRows 1162).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1162) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1162)
    (generalMeanRows_prefactorDomain 1162) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1162

/-! Kernel-checked entropy margins for general spectral rectangle 1163. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1163
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6436287917) (.branch 2 (.leaf 6254553038) (.leaf 6079981054))) (.branch 5 (.branch 4 (.leaf 5912170690) (.leaf 5750750034)) (.branch 6 (.leaf 5595373906) (.leaf 5445721501)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5301494284) (.leaf 5162414108)) (.branch 10 (.leaf 5028221510) (.leaf 4898674192))) (.branch 13 (.branch 12 (.leaf 4773545635) (.leaf 4652623851)) (.branch 14 (.leaf 4535710253) (.leaf 4422618627))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4313174194) (.branch 17 (.leaf 4207212761) (.leaf 4104579938))) (.branch 20 (.branch 19 (.leaf 4005130432) (.leaf 3908727392)) (.branch 21 (.leaf 3815241812) (.leaf 3724551987)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3636543003) (.leaf 3551106281)) (.branch 25 (.leaf 3468139142) (.leaf 3387544421))) (.branch 28 (.branch 27 (.leaf 3309230101) (.leaf 3233108975)) (.branch 29 (.leaf 3159098340) (.leaf 3087119706)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3017098535) (.branch 32 (.leaf 2948963988) (.leaf 2882648700))) (.branch 35 (.branch 34 (.leaf 2818088569) (.leaf 2755222553)) (.branch 36 (.leaf 2693992493) (.leaf 2634342937)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2576220985) (.leaf 2519576135)) (.branch 40 (.leaf 2464360151) (.leaf 2410526932))) (.branch 43 (.branch 42 (.leaf 2358032389) (.leaf 2306834336)) (.branch 44 (.leaf 2256892382) (.leaf 2208167835))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2160623609) (.branch 47 (.leaf 2114224137) (.leaf 2068935294))) (.branch 50 (.branch 49 (.leaf 2024724317) (.leaf 1981559733)) (.branch 51 (.leaf 1939411301) (.leaf 1898249939)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1858047672) (.leaf 1818777577)) (.branch 55 (.leaf 1780413725) (.leaf 1742931140))) (.branch 58 (.branch 57 (.leaf 1706305750) (.leaf 1670514340)) (.branch 59 (.leaf 1635534519) (.leaf 1601344675))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1567923943) (.branch 62 (.leaf 1535252169) (.leaf 1503309876))) (.branch 65 (.branch 64 (.leaf 1472078240) (.leaf 1441539054)) (.branch 66 (.leaf 1411674704) (.leaf 1382468147)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1353902879) (.leaf 1325962918)) (.branch 70 (.leaf 1298632780) (.leaf 1271897461))) (.branch 73 (.branch 72 (.leaf 1245742412) (.leaf 1220153526)) (.branch 74 (.leaf 1195117118) (.leaf 1170619908))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1146649007) (.branch 77 (.leaf 1123191901) (.leaf 1100236433))) (.branch 80 (.branch 79 (.leaf 1077770798) (.leaf 1055783521)) (.branch 81 (.leaf 1034263451) (.leaf 1013199746)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 992581862) (.leaf 972399545)) (.branch 85 (.leaf 952642817) (.leaf 933301971))) (.branch 88 (.branch 87 (.leaf 914367555) (.leaf 895830370)) (.branch 89 (.leaf 877681459) (.leaf 859912097)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 842513786) (.branch 92 (.leaf 825478247) (.leaf 808797410))) (.branch 95 (.branch 94 (.leaf 792463413) (.leaf 776468591)) (.branch 96 (.leaf 760805470) (.leaf 745466763)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 730445364) (.leaf 715734340)) (.branch 100 (.leaf 701326928) (.leaf 687216531))) (.branch 103 (.branch 102 (.leaf 673396711) (.leaf 659861183)) (.branch 104 (.leaf 646603816) (.leaf 633618622))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 620899755) (.leaf 608441510)) (.branch 108 (.leaf 596238312) (.leaf 584284719))) (.branch 111 (.branch 110 (.leaf 572575415) (.leaf 561105207)) (.branch 112 (.leaf 549869021) (.leaf 538861902)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 528079006) (.leaf 517515600)) (.branch 116 (.leaf 507167059) (.leaf 497028864))) (.branch 119 (.branch 118 (.leaf 487096596) (.leaf 477365936)) (.branch 120 (.leaf 467832661) (.leaf 458492645)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1163).prefactor = (5386986442960211/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1163).cutoff/(generalMeanRows 1163).c)).2 =
    (492275344786291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1163).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1163).q*(generalMeanRows 1163).cutoff/2-2 = (1557/608:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable390.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1163).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1163).criticalRate j.val*(generalMeanRows 1163).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1163).c*(generalMeanRows 1163).criticalPoint j.val)).2-
      (generalMeanRows 1163).J/2-(generalMeanRows 1163).error (generalMeanGrid j.val)+
      (generalMeanRows 1163).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1163).c)).2-
      (generalMeanRows 1163).J/2-(generalMeanRows 1163).error 4 := by
  have he : (generalMeanRows 1163).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1163) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1163)
    (generalMeanRows_prefactorDomain 1163) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1163

/-! Kernel-checked entropy margins for general spectral rectangle 1164. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1164
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6558209152) (.branch 2 (.leaf 6368255036) (.leaf 6185854994))) (.branch 5 (.branch 4 (.leaf 6010586819) (.leaf 5842059101)) (.branch 6 (.leaf 5679908462) (.leaf 5523797092)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5373410549) (.leaf 5228455778)) (.branch 10 (.leaf 5088659338) (.leaf 4953765800))) (.branch 13 (.branch 12 (.leaf 4823536303) (.leaf 4697747244)) (.branch 14 (.leaf 4576189093) (.leaf 4458665318))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4344991401) (.branch 17 (.leaf 4234993949) (.leaf 4128509872))) (.branch 20 (.branch 19 (.leaf 4025385648) (.leaf 3925476628)) (.branch 21 (.leaf 3828646420) (.leaf 3734766308)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3643714731) (.leaf 3555376789)) (.branch 25 (.leaf 3469643800) (.leaf 3386412889))) (.branch 28 (.branch 27 (.leaf 3305586603) (.leaf 3227072563)) (.branch 29 (.leaf 3150783132) (.leaf 3076635123)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3004549513) (.branch 32 (.leaf 2934451184) (.leaf 2866268686))) (.branch 35 (.branch 34 (.leaf 2799934014) (.leaf 2735382397)) (.branch 36 (.leaf 2672552109) (.leaf 2611384285)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2551822759) (.leaf 2493813904)) (.branch 40 (.leaf 2437306490) (.leaf 2382251545))) (.branch 43 (.branch 42 (.leaf 2328602229) (.leaf 2276313720)) (.branch 44 (.leaf 2225343097) (.leaf 2175649240))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2127192732) (.branch 47 (.leaf 2079935770) (.leaf 2033842079))) (.branch 50 (.branch 49 (.leaf 1988876830) (.leaf 1945006570)) (.branch 51 (.leaf 1902199147) (.leaf 1860423646)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1819650330) (.leaf 1779850577)) (.branch 55 (.leaf 1740996828) (.leaf 1703062535))) (.branch 58 (.branch 57 (.leaf 1666022112) (.leaf 1629850891)) (.branch 59 (.leaf 1594525076) (.leaf 1560021708))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1526318618) (.branch 62 (.leaf 1493394399) (.leaf 1461228370))) (.branch 65 (.branch 64 (.leaf 1429800539) (.leaf 1399091580)) (.branch 66 (.leaf 1369082797) (.leaf 1339756104)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1311093992) (.leaf 1283079511)) (.branch 70 (.leaf 1255696242) (.leaf 1228928277))) (.branch 73 (.branch 72 (.leaf 1202760201) (.leaf 1177177067)) (.branch 74 (.leaf 1152164380) (.leaf 1127708082))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1103794528) (.branch 77 (.leaf 1080410479) (.leaf 1057543078))) (.branch 80 (.branch 79 (.leaf 1035179842) (.leaf 1013308645)) (.branch 81 (.leaf 991917706) (.leaf 970995575)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 950531122) (.leaf 930513528)) (.branch 85 (.leaf 910932270) (.leaf 891777112))) (.branch 88 (.branch 87 (.leaf 873038096) (.leaf 854705533)) (.branch 89 (.leaf 836769993) (.leaf 819222295)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 802053500) (.branch 92 (.leaf 785254905) (.leaf 768818033))) (.branch 95 (.branch 94 (.leaf 752734625) (.leaf 736996635)) (.branch 96 (.leaf 721596223) (.leaf 706525748)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 691777762) (.leaf 677345004)) (.branch 100 (.leaf 663220394) (.leaf 649397030))) (.branch 103 (.branch 102 (.leaf 635868178) (.leaf 622627271)) (.branch 104 (.leaf 609667904) (.leaf 596983826))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 584568939) (.leaf 572417291)) (.branch 108 (.leaf 560523076) (.leaf 548880623))) (.branch 111 (.branch 110 (.leaf 537484400) (.leaf 526329004)) (.branch 112 (.leaf 515409161) (.leaf 504719720)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 494255654) (.leaf 484012051)) (.branch 116 (.leaf 473984113) (.leaf 464167156))) (.branch 119 (.branch 118 (.leaf 454556603) (.leaf 445147983)) (.branch 120 (.leaf 435936929) (.leaf 426919171)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1164).prefactor = (706006306893153/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1164).cutoff/(generalMeanRows 1164).c)).2 =
    (60218616474913/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1164).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1164).q*(generalMeanRows 1164).c/2-2 = (3269/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable386.value]
  have hcontinuation : (generalMeanRows 1164).q*(generalMeanRows 1164).cutoff/2-2 = (1557/608:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable390.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1164).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1164).criticalRate j.val*(generalMeanRows 1164).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1164).c*(generalMeanRows 1164).criticalPoint j.val)).2-
      (generalMeanRows 1164).J/2-(generalMeanRows 1164).error (generalMeanGrid j.val)+
      (generalMeanRows 1164).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1164).c)).2-
      (generalMeanRows 1164).J/2-(generalMeanRows 1164).error 4 := by
  have he : (generalMeanRows 1164).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1164) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1164)
    (generalMeanRows_prefactorDomain 1164) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1164

/-! Kernel-checked entropy margins for general spectral rectangle 1165. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1165
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6683064593) (.branch 2 (.leaf 6484636767) (.leaf 6294173188))) (.branch 5 (.branch 4 (.leaf 6111229561) (.leaf 5935393892)) (.branch 6 (.leaf 5766283595) (.leaf 5603542910)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5446840596) (.leaf 5295867859)) (.branch 10 (.leaf 5150336494) (.leaf 5009977208))) (.branch 13 (.branch 12 (.leaf 4874538104) (.leaf 4743783311)) (.branch 14 (.leaf 4617491744) (.leaf 4495455972))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4377481193) (.branch 17 (.leaf 4263384297) (.leaf 4152993012))) (.branch 20 (.branch 19 (.leaf 4046145121) (.leaf 3942687749)) (.branch 21 (.leaf 3842476702) (.leaf 3745375871)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3651256674) (.leaf 3559997547)) (.branch 25 (.leaf 3471483475) (.leaf 3385605560))) (.branch 28 (.branch 27 (.leaf 3302260622) (.leaf 3221350825)) (.branch 29 (.leaf 3142783341) (.leaf 3066470029)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2992327147) (.branch 32 (.leaf 2920275073) (.leaf 2850238061))) (.branch 35 (.branch 34 (.leaf 2782143998) (.leaf 2715924195)) (.branch 36 (.leaf 2651513177) (.leaf 2588848496)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2527870559) (.leaf 2468522458)) (.branch 40 (.leaf 2410749823) (.leaf 2354500675))) (.branch 43 (.branch 42 (.leaf 2299725294) (.leaf 2246376097)) (.branch 44 (.leaf 2194407515) (.leaf 2143775892))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2094439377) (.branch 47 (.leaf 2046357831) (.leaf 1999492736))) (.branch 50 (.branch 49 (.leaf 1953807112) (.leaf 1909265437)) (.branch 51 (.leaf 1865833576) (.leaf 1823478707)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1782169259) (.leaf 1741874849)) (.branch 55 (.leaf 1702566223) (.leaf 1664215206))) (.branch 58 (.branch 57 (.leaf 1626794646) (.leaf 1590278367)) (.branch 59 (.leaf 1554641125) (.leaf 1519858565))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1485907176) (.branch 62 (.leaf 1452764261) (.leaf 1420407893))) (.branch 65 (.branch 64 (.leaf 1388816884) (.leaf 1357970754)) (.branch 66 (.leaf 1327849699) (.leaf 1298434562)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1269706805) (.leaf 1241648485)) (.branch 70 (.leaf 1214242229) (.leaf 1187471209))) (.branch 73 (.branch 72 (.leaf 1161319121) (.leaf 1135770165)) (.branch 74 (.leaf 1110809024) (.leaf 1086420844))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1062591219) (.branch 77 (.leaf 1039306170) (.leaf 1016552133))) (.branch 80 (.branch 79 (.leaf 994315940) (.leaf 972584806)) (.branch 81 (.leaf 951346314) (.leaf 930588405)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 910299357) (.leaf 890467783)) (.branch 85 (.leaf 871082613) (.leaf 852133084))) (.branch 88 (.branch 87 (.leaf 833608731) (.leaf 815499373)) (.branch 89 (.leaf 797795109) (.leaf 780486304)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 763563584) (.branch 92 (.leaf 747017822) (.leaf 730840135))) (.branch 95 (.branch 94 (.leaf 715021874) (.leaf 699554618)) (.branch 96 (.leaf 684430164) (.leaf 669640523)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 655177911) (.leaf 641034745)) (.branch 100 (.leaf 627203634) (.leaf 613677377))) (.branch 103 (.branch 102 (.leaf 600448953) (.leaf 587511519)) (.branch 104 (.leaf 574858404) (.leaf 562483103))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 550379270) (.leaf 538540721)) (.branch 108 (.leaf 526961419) (.leaf 515635480))) (.branch 111 (.branch 110 (.leaf 504557160) (.leaf 493720857)) (.branch 112 (.leaf 483121105) (.leaf 472752569)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 462610043) (.leaf 452688446)) (.branch 116 (.leaf 442982819) (.leaf 433488322))) (.branch 119 (.branch 118 (.leaf 424200228) (.leaf 415113924)) (.branch 120 (.leaf 406224905) (.leaf 397528773)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1165).prefactor = (5921766145440027/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1165).cutoff/(generalMeanRows 1165).c)).2 =
    (58916521367631/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1165).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1165).q*(generalMeanRows 1165).c/2-2 = (3387/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable388.value]
  have hcontinuation : (generalMeanRows 1165).q*(generalMeanRows 1165).cutoff/2-2 = (1557/608:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable390.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1165).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1165).criticalRate j.val*(generalMeanRows 1165).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1165).c*(generalMeanRows 1165).criticalPoint j.val)).2-
      (generalMeanRows 1165).J/2-(generalMeanRows 1165).error (generalMeanGrid j.val)+
      (generalMeanRows 1165).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1165).c)).2-
      (generalMeanRows 1165).J/2-(generalMeanRows 1165).error 4 := by
  have he : (generalMeanRows 1165).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1165) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1165)
    (generalMeanRows_prefactorDomain 1165) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1165

/-! Kernel-checked entropy margins for general spectral rectangle 1166. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1166
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6327814261) (.branch 2 (.leaf 6150318368) (.leaf 5979795886))) (.branch 5 (.branch 4 (.leaf 5815851864) (.leaf 5658120727)) (.branch 6 (.leaf 5506263615) (.leaf 5359966002)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5218935579) (.leaf 5082900337)) (.branch 10 (.leaf 4951606868) (.leaf 4824818812))) (.branch 13 (.branch 12 (.leaf 4702315471) (.leaf 4583890551)) (.branch 14 (.leaf 4469351018) (.leaf 4358516065))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4251216173) (.branch 17 (.leaf 4147292251) (.leaf 4046594857))) (.branch 20 (.branch 19 (.leaf 3948983482) (.leaf 3854325903)) (.branch 21 (.leaf 3762497580) (.leaf 3673381109)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3586865725) (.leaf 3502846832)) (.branch 25 (.leaf 3421225587) (.leaf 3341908501))) (.branch 28 (.branch 27 (.leaf 3264807083) (.leaf 3189837510)) (.branch 29 (.leaf 3116920312) (.leaf 3045980098)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2976945285) (.branch 32 (.leaf 2909747862) (.leaf 2844323162))) (.branch 35 (.branch 34 (.leaf 2780609652) (.leaf 2718548745)) (.branch 36 (.leaf 2658084613) (.leaf 2599164028)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2541736199) (.leaf 2485752637)) (.branch 40 (.leaf 2431167010) (.leaf 2377935028))) (.branch 43 (.branch 42 (.leaf 2326014320) (.leaf 2275364328)) (.branch 44 (.leaf 2225946204) (.leaf 2177722717))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2130658164) (.branch 47 (.leaf 2084718287) (.leaf 2039870195))) (.branch 50 (.branch 49 (.leaf 1996082293) (.leaf 1953324213)) (.branch 51 (.leaf 1911566752) (.leaf 1870781811)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1830942340) (.leaf 1792022285)) (.branch 55 (.leaf 1753996540) (.leaf 1716840899))) (.branch 58 (.branch 57 (.leaf 1680532014) (.leaf 1645047355)) (.branch 59 (.leaf 1610365168) (.leaf 1576464444))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1543324879) (.branch 62 (.leaf 1510926848) (.leaf 1479251369))) (.branch 65 (.branch 64 (.leaf 1448280079) (.leaf 1417995204)) (.branch 66 (.leaf 1388379537) (.leaf 1359416407)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1331089667) (.leaf 1303383661)) (.branch 70 (.leaf 1276283211) (.leaf 1249773597))) (.branch 73 (.branch 72 (.leaf 1223840535) (.leaf 1198470163)) (.branch 74 (.leaf 1173649025) (.leaf 1149364052))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1125602549) (.branch 77 (.leaf 1102352182) (.leaf 1079600965))) (.branch 80 (.branch 79 (.leaf 1057337242) (.leaf 1035549684)) (.branch 81 (.leaf 1014227267) (.leaf 993359270)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 972935259) (.leaf 952945079)) (.branch 85 (.leaf 933378845) (.leaf 914226932))) (.branch 88 (.branch 87 (.leaf 895479965) (.leaf 877128814)) (.branch 89 (.leaf 859164583) (.leaf 841578603)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 824362428) (.branch 92 (.leaf 807507821) (.leaf 791006755))) (.branch 95 (.branch 94 (.leaf 774851403) (.leaf 759034129)) (.branch 96 (.leaf 743547489) (.leaf 728384220)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 713537234) (.leaf 698999618)) (.branch 100 (.leaf 684764624) (.leaf 670825665))) (.branch 103 (.branch 102 (.leaf 657176315) (.leaf 643810297)) (.branch 104 (.leaf 630721483) (.leaf 617903892))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 605351681) (.leaf 593059143)) (.branch 108 (.leaf 581020705) (.leaf 569230924))) (.branch 111 (.branch 110 (.leaf 557684480) (.leaf 546376178)) (.branch 112 (.leaf 535300941) (.leaf 524453807)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 513829928) (.leaf 503424565)) (.branch 116 (.leaf 493233088) (.leaf 483250969))) (.branch 119 (.branch 118 (.leaf 473473784) (.leaf 463897207)) (.branch 120 (.leaf 454517007) (.leaf 445329051)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1166).prefactor = (671583406024829/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1166).cutoff/(generalMeanRows 1166).c)).2 =
    (262699696105663/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1166).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1166).q*(generalMeanRows 1166).cutoff/2-2 = (787/288:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable391.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1166).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1166).criticalRate j.val*(generalMeanRows 1166).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1166).c*(generalMeanRows 1166).criticalPoint j.val)).2-
      (generalMeanRows 1166).J/2-(generalMeanRows 1166).error (generalMeanGrid j.val)+
      (generalMeanRows 1166).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1166).c)).2-
      (generalMeanRows 1166).J/2-(generalMeanRows 1166).error 4 := by
  have he : (generalMeanRows 1166).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1166) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1166)
    (generalMeanRows_prefactorDomain 1166) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1166

/-! Kernel-checked entropy margins for general spectral rectangle 1167. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1167
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6410984380) (.branch 2 (.leaf 6226538627) (.leaf 6049406784))) (.branch 5 (.branch 4 (.leaf 5879175602) (.leaf 5715462461)) (.branch 6 (.leaf 5557912601) (.leaf 5406196641)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5260008375) (.leaf 5119062781)) (.branch 10 (.leaf 4983094241) (.leaf 4851854937))) (.branch 13 (.branch 12 (.leaf 4725113396) (.leaf 4602653188)) (.branch 14 (.leaf 4484271729) (.leaf 4369779210))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4258997615) (.branch 17 (.leaf 4151759823) (.leaf 4047908805))) (.branch 20 (.branch 19 (.leaf 3947296870) (.leaf 3849784990)) (.branch 21 (.leaf 3755242179) (.leaf 3663544919)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3574576637) (.leaf 3488227224)) (.branch 25 (.leaf 3404392592) (.leaf 3322974268))) (.branch 28 (.branch 27 (.leaf 3243879015) (.leaf 3167018485)) (.branch 29 (.leaf 3092308904) (.leaf 3019670770)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2949028583) (.branch 32 (.leaf 2880310589) (.leaf 2813448547))) (.branch 35 (.branch 34 (.leaf 2748377511) (.leaf 2685035628)) (.branch 36 (.leaf 2623363948) (.leaf 2563306255)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2504808899) (.leaf 2447820649)) (.branch 40 (.leaf 2392292551) (.leaf 2338177798))) (.branch 43 (.branch 42 (.leaf 2285431607) (.leaf 2234011107)) (.branch 44 (.leaf 2183875230) (.leaf 2134984615))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2087301514) (.branch 47 (.leaf 2040789703) (.leaf 1995414404))) (.branch 50 (.branch 49 (.leaf 1951142210) (.leaf 1907941010)) (.branch 51 (.leaf 1865779924) (.leaf 1824629241)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1784460363) (.leaf 1745245744)) (.branch 55 (.leaf 1706958843) (.leaf 1669574074))) (.branch 58 (.branch 57 (.leaf 1633066758) (.leaf 1597413086)) (.branch 59 (.leaf 1562590072) (.leaf 1528575518))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1495347980) (.branch 62 (.leaf 1462886729) (.leaf 1431171723))) (.branch 65 (.branch 64 (.leaf 1400183577) (.leaf 1369903532)) (.branch 66 (.leaf 1340313430) (.leaf 1311395687)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1283133271) (.leaf 1255509679)) (.branch 70 (.leaf 1228508911) (.leaf 1202115458))) (.branch 73 (.branch 72 (.leaf 1176314274) (.leaf 1151090763)) (.branch 74 (.leaf 1126430759) (.leaf 1102320511))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1078746666) (.branch 77 (.leaf 1055696257) (.leaf 1033156682))) (.branch 80 (.branch 79 (.leaf 1011115699) (.leaf 989561407)) (.branch 81 (.leaf 968482236) (.leaf 947866935)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 927704560) (.leaf 907984466)) (.branch 85 (.leaf 888696293) (.leaf 869829961))) (.branch 88 (.branch 87 (.leaf 851375653) (.leaf 833323817)) (.branch 89 (.leaf 815665148) (.leaf 798390583)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 781491296) (.branch 92 (.leaf 764958688) (.leaf 748784377))) (.branch 95 (.branch 94 (.leaf 732960198) (.leaf 717478191)) (.branch 96 (.leaf 702330595) (.leaf 687509845)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 673008565) (.leaf 658819560)) (.branch 100 (.leaf 644935812) (.leaf 631350478))) (.branch 103 (.branch 102 (.leaf 618056880) (.leaf 605048502)) (.branch 104 (.leaf 592318989) (.leaf 579862134))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 567671885) (.leaf 555742331)) (.branch 108 (.leaf 544067702) (.leaf 532642367))) (.branch 111 (.branch 110 (.leaf 521460826) (.leaf 510517711)) (.branch 112 (.leaf 499807778) (.leaf 489325907)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 479067098) (.leaf 469026466)) (.branch 116 (.leaf 459199240) (.leaf 449580761))) (.branch 119 (.branch 118 (.leaf 440166473) (.leaf 430951931)) (.branch 120 (.leaf 421932787) (.leaf 413104795)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1167).prefactor = (5600768411503257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1167).cutoff/(generalMeanRows 1167).c)).2 =
    (32193126409529/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1167).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1167).q*(generalMeanRows 1167).c/2-2 = (331/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable296.value]
  have hcontinuation : (generalMeanRows 1167).q*(generalMeanRows 1167).cutoff/2-2 = (787/288:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable391.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1167).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1167).criticalRate j.val*(generalMeanRows 1167).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1167).c*(generalMeanRows 1167).criticalPoint j.val)).2-
      (generalMeanRows 1167).J/2-(generalMeanRows 1167).error (generalMeanGrid j.val)+
      (generalMeanRows 1167).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1167).c)).2-
      (generalMeanRows 1167).J/2-(generalMeanRows 1167).error 4 := by
  have he : (generalMeanRows 1167).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1167) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1167)
    (generalMeanRows_prefactorDomain 1167) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1167

/-! Kernel-checked entropy margins for general spectral rectangle 1168. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1168
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6588737697) (.branch 2 (.leaf 6396808062) (.leaf 6212525242))) (.branch 5 (.branch 4 (.leaf 6035457620) (.leaf 5865205516)) (.branch 6 (.leaf 5701398294) (.leaf 5543691792)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5391766010) (.leaf 5245323046)) (.branch 10 (.leaf 5104085237) (.leaf 4967793490))) (.branch 13 (.branch 12 (.leaf 4836205764) (.leaf 4709095712)) (.branch 14 (.leaf 4586251440) (.leaf 4467474380))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4352578277) (.branch 17 (.leaf 4241388252) (.leaf 4133739954))) (.branch 20 (.branch 19 (.leaf 4029478788) (.leaf 3928459207)) (.branch 21 (.leaf 3830544059) (.leaf 3735603993)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3643516918) (.leaf 3554167492)) (.branch 25 (.leaf 3467446670) (.leaf 3383251272))) (.branch 28 (.branch 27 (.leaf 3301483591) (.leaf 3222051038)) (.branch 29 (.leaf 3144865799) (.leaf 3069844533)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2996908084) (.branch 32 (.leaf 2925981215) (.leaf 2856992367))) (.branch 35 (.branch 34 (.leaf 2789873428) (.leaf 2724559523)) (.branch 36 (.leaf 2660988819) (.leaf 2599102343)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2538843814) (.leaf 2480159481)) (.branch 40 (.leaf 2422997980) (.leaf 2367310200))) (.branch 43 (.branch 42 (.leaf 2313049148) (.leaf 2260169836)) (.branch 44 (.leaf 2208629170) (.leaf 2158385842))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2109400237) (.branch 47 (.leaf 2061634344) (.leaf 2015051663))) (.branch 50 (.branch 49 (.leaf 1969617136) (.leaf 1925297065)) (.branch 51 (.leaf 1882059047) (.leaf 1839871903)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1798705625) (.leaf 1758531311)) (.branch 55 (.leaf 1719321112) (.leaf 1681048186))) (.branch 58 (.branch 57 (.leaf 1643686645) (.leaf 1607211511)) (.branch 59 (.leaf 1571598676) (.leaf 1536824859))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1502867571) (.branch 62 (.leaf 1469705076) (.leaf 1437316363))) (.branch 65 (.branch 64 (.leaf 1405681108) (.leaf 1374779649)) (.branch 66 (.leaf 1344592955) (.leaf 1315102602)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1286290742) (.leaf 1258140088)) (.branch 70 (.leaf 1230633883) (.leaf 1203755884))) (.branch 73 (.branch 72 (.leaf 1177490336) (.leaf 1151821961)) (.branch 74 (.leaf 1126735931) (.leaf 1102217856))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1078253767) (.branch 77 (.leaf 1054830096) (.leaf 1031933668))) (.branch 80 (.branch 79 (.leaf 1009551679) (.leaf 987671688)) (.branch 81 (.leaf 966281605) (.leaf 945369670)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 924924454) (.leaf 904934836)) (.branch 85 (.leaf 885389999) (.leaf 866279418))) (.branch 88 (.branch 87 (.leaf 847592851) (.leaf 829320328)) (.branch 89 (.leaf 811452143) (.leaf 793978845)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 776891232) (.branch 92 (.leaf 760180338) (.leaf 743837431))) (.branch 95 (.branch 94 (.leaf 727854003) (.leaf 712221764)) (.branch 96 (.leaf 696932634) (.leaf 681978737)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 667352397) (.leaf 653046128)) (.branch 100 (.leaf 639052632) (.leaf 625364793))) (.branch 103 (.branch 102 (.leaf 611975669) (.leaf 598878489)) (.branch 104 (.leaf 586066651) (.leaf 573533709))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 561273378) (.leaf 549279524)) (.branch 108 (.leaf 537546159) (.leaf 526067442))) (.branch 111 (.branch 110 (.leaf 514837669) (.leaf 503851275)) (.branch 112 (.leaf 493102826) (.leaf 482587017)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 472298668) (.leaf 462232721)) (.branch 116 (.leaf 452384240) (.leaf 442748399))) (.branch 119 (.branch 118 (.leaf 433320491) (.leaf 424095914)) (.branch 120 (.leaf 415070176) (.leaf 406238888)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1168).prefactor = (91227403186617/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1168).cutoff/(generalMeanRows 1168).c)).2 =
    (509974921885693/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1168).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1168).q*(generalMeanRows 1168).cutoff/2-2 = (787/288:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable391.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1168).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1168).criticalRate j.val*(generalMeanRows 1168).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1168).c*(generalMeanRows 1168).criticalPoint j.val)).2-
      (generalMeanRows 1168).J/2-(generalMeanRows 1168).error (generalMeanGrid j.val)+
      (generalMeanRows 1168).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1168).c)).2-
      (generalMeanRows 1168).J/2-(generalMeanRows 1168).error 4 := by
  have he : (generalMeanRows 1168).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1168) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1168)
    (generalMeanRows_prefactorDomain 1168) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1168

/-! Kernel-checked entropy margins for general spectral rectangle 1169. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1169
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6771556832) (.branch 2 (.leaf 6571867903) (.leaf 6380173223))) (.branch 5 (.branch 4 (.leaf 6196021976) (.leaf 6018996645)) (.branch 6 (.leaf 5848710003) (.leaf 5684802428)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5526939498) (.leaf 5374809843)) (.branch 10 (.leaf 5228123203) (.leaf 5086608691))) (.branch 13 (.branch 12 (.leaf 4950013214) (.leaf 4818100050)) (.branch 14 (.leaf 4690647565) (.leaf 4567448032))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4448306574) (.branch 17 (.leaf 4333040192) (.leaf 4221476880))) (.branch 20 (.branch 19 (.leaf 4113454818) (.leaf 4008821636)) (.branch 21 (.leaf 3907433731) (.leaf 3809155652)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3713859530) (.leaf 3621424554)) (.branch 25 (.leaf 3531736486) (.leaf 3444687224))) (.branch 28 (.branch 27 (.leaf 3360174388) (.leaf 3278100947)) (.branch 29 (.leaf 3198374865) (.leaf 3120908784)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3045619725) (.branch 32 (.leaf 2972428809) (.leaf 2901261005))) (.branch 35 (.branch 34 (.leaf 2832044891) (.leaf 2764712435)) (.branch 36 (.leaf 2699198789) (.leaf 2635442100)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2573383334) (.leaf 2512966109)) (.branch 40 (.leaf 2454136546) (.leaf 2396843122))) (.branch 43 (.branch 42 (.leaf 2341036538) (.leaf 2286669599)) (.branch 44 (.leaf 2233697090) (.leaf 2182075676))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2131763795) (.branch 47 (.leaf 2082721564) (.leaf 2034910694))) (.branch 50 (.branch 49 (.leaf 1988294403) (.leaf 1942837339)) (.branch 51 (.leaf 1898505509) (.leaf 1855266210)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1813087960) (.leaf 1771940446)) (.branch 55 (.leaf 1731794460) (.leaf 1692621851))) (.branch 58 (.branch 57 (.leaf 1654395472) (.leaf 1617089131)) (.branch 59 (.leaf 1580677552) (.leaf 1545136328))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1510441885) (.branch 62 (.leaf 1476571443) (.leaf 1443502980))) (.branch 65 (.branch 64 (.leaf 1411215200) (.leaf 1379687505)) (.branch 66 (.leaf 1348899957) (.leaf 1318833259)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1289468723) (.leaf 1260788244)) (.branch 70 (.leaf 1232774282) (.leaf 1205409834))) (.branch 73 (.branch 72 (.leaf 1178678416) (.leaf 1152564038)) (.branch 74 (.leaf 1127051190) (.leaf 1102124823))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1077770327) (.branch 77 (.leaf 1053973520) (.leaf 1030720627))) (.branch 80 (.branch 79 (.leaf 1007998271) (.leaf 985793453)) (.branch 81 (.leaf 964093543) (.leaf 942886262)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 922159674) (.leaf 901902173)) (.branch 85 (.leaf 882102471) (.leaf 862749588))) (.branch 88 (.branch 87 (.leaf 843832838) (.leaf 825341826)) (.branch 89 (.leaf 807266434) (.leaf 789596812)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 772323369) (.branch 92 (.leaf 755436768) (.leaf 738927915))) (.branch 95 (.branch 94 (.leaf 722787951) (.leaf 707008248)) (.branch 96 (.leaf 691580398) (.leaf 676496208)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 661747695) (.leaf 647327076)) (.branch 100 (.leaf 633226767) (.leaf 619439372))) (.branch 103 (.branch 102 (.leaf 605957680) (.leaf 592774662)) (.branch 104 (.leaf 579883460) (.leaf 567277387))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 554949921) (.leaf 542894699)) (.branch 108 (.leaf 531105513) (.leaf 519576307))) (.branch 111 (.branch 110 (.leaf 508301172) (.leaf 497274341)) (.branch 112 (.leaf 486490187) (.leaf 475943216)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 465628069) (.leaf 455539512)) (.branch 116 (.leaf 445672438) (.leaf 436021859))) (.branch 119 (.branch 118 (.leaf 426582906) (.leaf 417350827)) (.branch 120 (.leaf 408320979) (.leaf 399488829)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1169).prefactor = (6086434577714221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1169).cutoff/(generalMeanRows 1169).c)).2 =
    (504885852378221/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1169).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1169).q*(generalMeanRows 1169).cutoff/2-2 = (787/288:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable391.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1169).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1169).criticalRate j.val*(generalMeanRows 1169).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1169).c*(generalMeanRows 1169).criticalPoint j.val)).2-
      (generalMeanRows 1169).J/2-(generalMeanRows 1169).error (generalMeanGrid j.val)+
      (generalMeanRows 1169).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1169).c)).2-
      (generalMeanRows 1169).J/2-(generalMeanRows 1169).error 4 := by
  have he : (generalMeanRows 1169).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1169) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1169)
    (generalMeanRows_prefactorDomain 1169) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1169

/-! Kernel-checked entropy margins for general spectral rectangle 1170. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1170
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6670361706) (.branch 2 (.leaf 6464086509) (.leaf 6266233957))) (.branch 5 (.branch 4 (.leaf 6076330291) (.leaf 5893936519)) (.branch 6 (.leaf 5718645274) (.leaf 5550078030)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5387882595) (.leaf 5231730871)) (.branch 10 (.leaf 5081316844) (.leaf 4936354760))) (.branch 13 (.branch 12 (.leaf 4796577498) (.leaf 4661735077)) (.branch 14 (.leaf 4531593318) (.leaf 4405932624))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4284546870) (.branch 17 (.leaf 4167242392) (.leaf 4053837065))) (.branch 20 (.branch 19 (.leaf 3944159463) (.leaf 3838048087)) (.branch 21 (.leaf 3735350658) (.leaf 3635923471)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3539630803) (.leaf 3446344361)) (.branch 25 (.leaf 3355942783) (.leaf 3268311175))) (.branch 28 (.branch 27 (.leaf 3183340680) (.leaf 3100928089)) (.branch 29 (.leaf 3020975471) (.leaf 2943389839)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2868082840) (.branch 32 (.leaf 2794970460) (.leaf 2723972762))) (.branch 35 (.branch 34 (.leaf 2655013634) (.leaf 2588020560)) (.branch 36 (.leaf 2522924405) (.leaf 2459659213)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2398162028) (.leaf 2338372712)) (.branch 40 (.leaf 2280233793) (.leaf 2223690307))) (.branch 43 (.branch 42 (.leaf 2168689664) (.leaf 2115181514)) (.branch 44 (.leaf 2063117624) (.leaf 2012451766))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1963139610) (.branch 47 (.leaf 1915138622) (.leaf 1868407971))) (.branch 50 (.branch 49 (.leaf 1822908442) (.leaf 1778602353)) (.branch 51 (.leaf 1735453478) (.leaf 1693426974)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1652489314) (.leaf 1612608220)) (.branch 55 (.leaf 1573752607) (.leaf 1535892524))) (.branch 58 (.branch 57 (.leaf 1498999099) (.leaf 1463044493)) (.branch 59 (.leaf 1428001849) (.leaf 1393845248))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1360549668) (.branch 62 (.leaf 1328090944) (.leaf 1296445729))) (.branch 65 (.branch 64 (.leaf 1265591460) (.leaf 1235506325)) (.branch 66 (.leaf 1206169227) (.leaf 1177559760)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1149658176) (.leaf 1122445359)) (.branch 70 (.leaf 1095902802) (.leaf 1070012578))) (.branch 73 (.branch 72 (.leaf 1044757320) (.leaf 1020120200)) (.branch 74 (.leaf 996084904) (.leaf 972635617))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 949757002) (.branch 77 (.leaf 927434181) (.leaf 905652720))) (.branch 80 (.branch 79 (.leaf 884398610) (.leaf 863658254)) (.branch 81 (.leaf 843418454) (.leaf 823666389)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 804389613) (.leaf 785576031)) (.branch 85 (.leaf 767213893) (.leaf 749291783))) (.branch 88 (.branch 87 (.leaf 731798603) (.leaf 714723565)) (.branch 89 (.leaf 698056182) (.leaf 681786257)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 665903869) (.branch 92 (.leaf 650399374) (.leaf 635263387))) (.branch 95 (.branch 94 (.leaf 620486776) (.leaf 606060658)) (.branch 96 (.leaf 591976385) (.leaf 578225543)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564799940) (.leaf 551691601)) (.branch 100 (.leaf 538892761) (.leaf 526395859))) (.branch 103 (.branch 102 (.leaf 514193533) (.leaf 502278612)) (.branch 104 (.leaf 490644111) (.leaf 479283225))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 468189327) (.leaf 457355959)) (.branch 108 (.leaf 446776828) (.leaf 436445801))) (.branch 111 (.branch 110 (.leaf 426356905) (.leaf 416504314)) (.branch 112 (.leaf 406882353) (.leaf 397485489)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388308327) (.leaf 379345611)) (.branch 116 (.leaf 370592214) (.leaf 362043137))) (.branch 119 (.branch 118 (.leaf 353693508) (.leaf 345538574)) (.branch 120 (.leaf 337573701) (.leaf 329794370)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1170).prefactor = (6344839340826923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1170).cutoff/(generalMeanRows 1170).c)).2 =
    (484784673057133/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1170).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1170).q*(generalMeanRows 1170).cutoff/2-2 = (787/288:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable391.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1170).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1170).criticalRate j.val*(generalMeanRows 1170).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1170).c*(generalMeanRows 1170).criticalPoint j.val)).2-
      (generalMeanRows 1170).J/2-(generalMeanRows 1170).error (generalMeanGrid j.val)+
      (generalMeanRows 1170).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1170).c)).2-
      (generalMeanRows 1170).J/2-(generalMeanRows 1170).error 4 := by
  have he : (generalMeanRows 1170).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1170) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1170)
    (generalMeanRows_prefactorDomain 1170) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1170

/-! Kernel-checked entropy margins for general spectral rectangle 1171. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1171
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6570060319) (.branch 2 (.leaf 6384043557) (.leaf 6205333436))) (.branch 5 (.branch 4 (.leaf 6033513129) (.leaf 5868197282)) (.branch 6 (.leaf 5709029135) (.leaf 5555677942)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5407836667) (.leaf 5265219927)) (.branch 10 (.leaf 5127562133) (.leaf 4994615830))) (.branch 13 (.branch 12 (.leaf 4866150186) (.leaf 4741949636)) (.branch 14 (.leaf 4621812657) (.leaf 4505550646))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4392986910) (.branch 17 (.leaf 4283955748) (.leaf 4178301611))) (.branch 20 (.branch 19 (.leaf 4075878335) (.leaf 3976548445)) (.branch 21 (.leaf 3880182517) (.leaf 3786658592)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3695861642) (.leaf 3607683078)) (.branch 25 (.leaf 3522020299) (.leaf 3438776277))) (.branch 28 (.branch 27 (.leaf 3357859178) (.leaf 3279182008)) (.branch 29 (.leaf 3202662289) (.leaf 3128221763)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3055786114) (.branch 32 (.leaf 2985284716) (.leaf 2916650392))) (.branch 35 (.branch 34 (.leaf 2849819202) (.leaf 2784730239)) (.branch 36 (.leaf 2721325438) (.leaf 2659549410)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2599349274) (.leaf 2540674513)) (.branch 40 (.leaf 2483476828) (.leaf 2427710017))) (.branch 43 (.branch 42 (.leaf 2373329850) (.leaf 2320293955)) (.branch 44 (.leaf 2268561720) (.leaf 2218094190))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2168853978) (.branch 47 (.leaf 2120805181) (.leaf 2073913300))) (.branch 50 (.branch 49 (.leaf 2028145168) (.leaf 1983468876)) (.branch 51 (.leaf 1939853714) (.leaf 1897270106)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1855689557) (.leaf 1815084594)) (.branch 55 (.leaf 1775428723) (.leaf 1736696376))) (.branch 58 (.branch 57 (.leaf 1698862872) (.leaf 1661904372)) (.branch 59 (.leaf 1625797839) (.leaf 1590521008))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1556052342) (.branch 62 (.leaf 1522371008) (.leaf 1489456841))) (.branch 65 (.branch 64 (.leaf 1457290317) (.leaf 1425852525)) (.branch 66 (.leaf 1395125144) (.leaf 1365090413)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1335731113) (.leaf 1307030543)) (.branch 70 (.leaf 1278972499) (.leaf 1251541257))) (.branch 73 (.branch 72 (.leaf 1224721549) (.leaf 1198498553)) (.branch 74 (.leaf 1172857869) (.leaf 1147785508))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1123267875) (.branch 77 (.leaf 1099291753) (.leaf 1075844293))) (.branch 80 (.branch 79 (.leaf 1052913000) (.leaf 1030485716)) (.branch 81 (.leaf 1008550617) (.leaf 987096191)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 966111237) (.leaf 945584850)) (.branch 85 (.leaf 925506410) (.leaf 905865577))) (.branch 88 (.branch 87 (.leaf 886652275) (.leaf 867856693)) (.branch 89 (.leaf 849469269) (.leaf 831480684)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 813881856) (.branch 92 (.leaf 796663933) (.leaf 779818282))) (.branch 95 (.branch 94 (.leaf 763336488) (.leaf 747210343)) (.branch 96 (.leaf 731431843) (.leaf 715993179)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 700886735) (.leaf 686105078)) (.branch 100 (.leaf 671640958) (.leaf 657487297))) (.branch 103 (.branch 102 (.leaf 643637189) (.leaf 630083893)) (.branch 104 (.leaf 616820830) (.leaf 603841575))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 591139856) (.leaf 578709550)) (.branch 108 (.leaf 566544677) (.leaf 554639398))) (.branch 111 (.branch 110 (.leaf 542988010) (.leaf 531584943)) (.branch 112 (.leaf 520424756) (.leaf 509502135)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 498811886) (.leaf 488348940)) (.branch 116 (.leaf 478108338) (.leaf 468085240))) (.branch 119 (.branch 118 (.leaf 458274914) (.leaf 448672736)) (.branch 120 (.leaf 439274189) (.leaf 430074855)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1171).prefactor = (5757373448701411/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1171).cutoff/(generalMeanRows 1171).c)).2 =
    (34653680926807/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1171).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1171).q*(generalMeanRows 1171).c/2-2 = (6629/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable392.value]
  have hcontinuation : (generalMeanRows 1171).q*(generalMeanRows 1171).cutoff/2-2 = (1591/544:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable393.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1171).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1171).criticalRate j.val*(generalMeanRows 1171).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1171).c*(generalMeanRows 1171).criticalPoint j.val)).2-
      (generalMeanRows 1171).J/2-(generalMeanRows 1171).error (generalMeanGrid j.val)+
      (generalMeanRows 1171).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1171).c)).2-
      (generalMeanRows 1171).J/2-(generalMeanRows 1171).error 4 := by
  have he : (generalMeanRows 1171).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1171) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1171)
    (generalMeanRows_prefactorDomain 1171) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1171

/-! Kernel-checked entropy margins for general spectral rectangle 1172. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1172
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7115743568) (.branch 2 (.leaf 6921855428) (.leaf 6735475703))) (.branch 5 (.branch 4 (.leaf 6556174323) (.leaf 6383553877)) (.branch 6 (.leaf 6217246611) (.leaf 6056911750)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5902233104) (.leaf 5752916922)) (.branch 10 (.leaf 5608689965) (.leaf 5469297779))) (.branch 13 (.branch 12 (.leaf 5334503123) (.leaf 5204084562)) (.branch 14 (.leaf 5077835190) (.leaf 4955561468))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4837082175) (.branch 17 (.leaf 4722227450) (.leaf 4610837921))) (.branch 20 (.branch 19 (.leaf 4502763912) (.leaf 4397864716)) (.branch 21 (.leaf 4296007934) (.leaf 4197068868)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4100929965) (.leaf 4007480307)) (.branch 25 (.leaf 3916615145) (.leaf 3828235466))) (.branch 28 (.branch 27 (.leaf 3742247601) (.leaf 3658562856)) (.branch 29 (.leaf 3577097182) (.leaf 3497770863)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3420508230) (.branch 32 (.leaf 3345237397) (.leaf 3271890019))) (.branch 35 (.branch 34 (.leaf 3200401066) (.leaf 3130708612)) (.branch 36 (.leaf 3062753643) (.leaf 2996479878)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2931833605) (.leaf 2868763519)) (.branch 40 (.leaf 2807220588) (.leaf 2747157912))) (.branch 43 (.branch 42 (.leaf 2688530602) (.leaf 2631295667)) (.branch 44 (.leaf 2575411902) (.leaf 2520839790))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2467541409) (.branch 47 (.leaf 2415480343) (.leaf 2364621603))) (.branch 50 (.branch 49 (.leaf 2314931550) (.leaf 2266377821)) (.branch 51 (.leaf 2218929269) (.leaf 2172555895)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2127228792) (.leaf 2082920090)) (.branch 55 (.leaf 2039602906) (.leaf 1997251294))) (.branch 58 (.branch 57 (.leaf 1955840201) (.leaf 1915345425)) (.branch 59 (.leaf 1875743576) (.leaf 1837012035))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1799128924) (.branch 62 (.leaf 1762073068) (.leaf 1725823968))) (.branch 65 (.branch 64 (.leaf 1690361768) (.leaf 1655667229)) (.branch 66 (.leaf 1621721703) (.leaf 1588507108)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1556005903) (.leaf 1524201070)) (.branch 70 (.leaf 1493076088) (.leaf 1462614917))) (.branch 73 (.branch 72 (.leaf 1432801977) (.leaf 1403622131)) (.branch 74 (.leaf 1375060671) (.leaf 1347103294))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1319736098) (.branch 77 (.leaf 1292945556) (.leaf 1266718511))) (.branch 80 (.branch 79 (.leaf 1241042160) (.leaf 1215904039)) (.branch 81 (.leaf 1191292016) (.leaf 1167194275)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1143599309) (.leaf 1120495907)) (.branch 85 (.leaf 1097873146) (.leaf 1075720380))) (.branch 88 (.branch 87 (.leaf 1054027232) (.leaf 1032783587)) (.branch 89 (.leaf 1011979579) (.leaf 991605590)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 971652236) (.branch 92 (.leaf 952110363) (.leaf 932971039))) (.branch 95 (.branch 94 (.leaf 914225551) (.leaf 895865391)) (.branch 96 (.leaf 877882257) (.leaf 860268045)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 843014840) (.leaf 826114918)) (.branch 100 (.leaf 809560730) (.leaf 793344909))) (.branch 103 (.branch 102 (.leaf 777460256) (.leaf 761899737)) (.branch 104 (.leaf 746656484) (.leaf 731723784))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 717095078) (.leaf 702763955)) (.branch 108 (.leaf 688724151) (.leaf 674969543))) (.branch 111 (.branch 110 (.leaf 661494146) (.leaf 648292108)) (.branch 112 (.leaf 635357710) (.leaf 622685359)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 610269586) (.leaf 598105045)) (.branch 116 (.leaf 586186507) (.leaf 574508857))) (.branch 119 (.branch 118 (.leaf 563067094) (.leaf 551856326)) (.branch 120 (.leaf 540871769) (.leaf 530108742)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1172).prefactor = (2987404514141331/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1172).cutoff/(generalMeanRows 1172).c)).2 =
    (569687615530739/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1172).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1172).q*(generalMeanRows 1172).c/2-2 = (6287/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable394.value]
  have hcontinuation : (generalMeanRows 1172).q*(generalMeanRows 1172).cutoff/2-2 = (1591/544:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable393.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1172).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1172).criticalRate j.val*(generalMeanRows 1172).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1172).c*(generalMeanRows 1172).criticalPoint j.val)).2-
      (generalMeanRows 1172).J/2-(generalMeanRows 1172).error (generalMeanGrid j.val)+
      (generalMeanRows 1172).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1172).c)).2-
      (generalMeanRows 1172).J/2-(generalMeanRows 1172).error 4 := by
  have he : (generalMeanRows 1172).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1172) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1172)
    (generalMeanRows_prefactorDomain 1172) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1172

/-! Kernel-checked entropy margins for general spectral rectangle 1173. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1173
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7594489479) (.branch 2 (.leaf 7395655209) (.leaf 7204417882))) (.branch 5 (.branch 4 (.leaf 7020340136) (.leaf 6843018012)) (.branch 6 (.leaf 6672077875) (.leaf 6507173670)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6347984466) (.leaf 6194212263)) (.branch 10 (.leaf 6045580014) (.leaf 5901829850))) (.branch 13 (.branch 12 (.leaf 5762721481) (.leaf 5628030745)) (.branch 14 (.leaf 5497548303) (.leaf 5371078449))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5248438037) (.branch 17 (.leaf 5129455497) (.leaf 5013969945))) (.branch 20 (.branch 19 (.leaf 4901830371) (.leaf 4792894896)) (.branch 21 (.leaf 4687030094) (.leaf 4584110369)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4484017391) (.leaf 4386639569)) (.branch 25 (.leaf 4291871579) (.leaf 4199613919))) (.branch 28 (.branch 27 (.leaf 4109772506) (.leaf 4022258306)) (.branch 29 (.leaf 3936986988) (.leaf 3853878612)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3772857333) (.branch 32 (.leaf 3693851135) (.leaf 3616791578))) (.branch 35 (.branch 34 (.leaf 3541613574) (.leaf 3468255169)) (.branch 36 (.leaf 3396657348) (.leaf 3326763850)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3258521002) (.leaf 3191877560)) (.branch 40 (.leaf 3126784559) (.leaf 3063195186))) (.branch 43 (.branch 42 (.leaf 3001064645) (.leaf 2940350044)) (.branch 44 (.leaf 2881010287) (.leaf 2823005969))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2766299282) (.branch 47 (.leaf 2710853928) (.leaf 2656635035))) (.branch 50 (.branch 49 (.leaf 2603609081) (.leaf 2551743820)) (.branch 51 (.leaf 2501008217) (.leaf 2451372386)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2402807527) (.leaf 2355285873)) (.branch 55 (.leaf 2308780642) (.leaf 2263265981))) (.branch 58 (.branch 57 (.leaf 2218716926) (.leaf 2175109360)) (.branch 59 (.leaf 2132419969) (.leaf 2090626207))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2049706259) (.branch 62 (.leaf 2009639011) (.leaf 1970404014))) (.branch 65 (.branch 64 (.leaf 1931981458) (.leaf 1894352144)) (.branch 66 (.leaf 1857497455) (.leaf 1821399335)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1786040261) (.leaf 1751403226)) (.branch 70 (.leaf 1717471716) (.leaf 1684229688))) (.branch 73 (.branch 72 (.leaf 1651661555) (.leaf 1619752165)) (.branch 74 (.leaf 1588486788) (.leaf 1557851097))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1527831152) (.branch 77 (.leaf 1498413391) (.leaf 1469584610))) (.branch 80 (.branch 79 (.leaf 1441331954) (.leaf 1413642904)) (.branch 81 (.leaf 1386505265) (.leaf 1359907153)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1333836988) (.leaf 1308283483)) (.branch 85 (.leaf 1283235629) (.leaf 1258682695))) (.branch 88 (.branch 87 (.leaf 1234614211) (.leaf 1211019964)) (.branch 89 (.leaf 1187889989) (.leaf 1165214560)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1142984185) (.branch 92 (.leaf 1121189597) (.leaf 1099821747))) (.branch 95 (.branch 94 (.leaf 1078871799) (.leaf 1058331123)) (.branch 96 (.leaf 1038191289) (.leaf 1018444062)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 999081394) (.leaf 980095422)) (.branch 100 (.leaf 961478460) (.leaf 943222997))) (.branch 103 (.branch 102 (.leaf 925321689) (.leaf 907767357)) (.branch 104 (.leaf 890552982) (.leaf 873671699))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 857116794) (.leaf 840881704)) (.branch 108 (.leaf 824960004) (.leaf 809345414))) (.branch 111 (.branch 110 (.leaf 794031786) (.leaf 779013108)) (.branch 112 (.leaf 764283496) (.leaf 749837191)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 735668559) (.leaf 721772086)) (.branch 116 (.leaf 708142374) (.leaf 694774140))) (.branch 119 (.branch 118 (.leaf 681662212) (.leaf 668801527)) (.branch 120 (.leaf 656187128) (.leaf 643814163)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1173).prefactor = (6109192435440917/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1173).cutoff/(generalMeanRows 1173).c)).2 =
    (585151841228321/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1173).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1173).q*(generalMeanRows 1173).cutoff/2-2 = (1591/544:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable393.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1173).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1173).criticalRate j.val*(generalMeanRows 1173).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1173).c*(generalMeanRows 1173).criticalPoint j.val)).2-
      (generalMeanRows 1173).J/2-(generalMeanRows 1173).error (generalMeanGrid j.val)+
      (generalMeanRows 1173).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1173).c)).2-
      (generalMeanRows 1173).J/2-(generalMeanRows 1173).error 4 := by
  have he : (generalMeanRows 1173).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1173) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1173)
    (generalMeanRows_prefactorDomain 1173) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1173

/-! Kernel-checked entropy margins for general spectral rectangle 1174. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1174
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5973710831) (.branch 2 (.leaf 5779228162) (.leaf 5592870359))) (.branch 5 (.branch 4 (.leaf 5414176817) (.leaf 5242721003)) (.branch 6 (.leaf 5078107368) (.leaf 4919968588)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4767963094) (.leaf 4621772867)) (.branch 10 (.leaf 4481101445) (.leaf 4345672135))) (.branch 13 (.branch 12 (.leaf 4215226400) (.leaf 4089522400)) (.branch 14 (.leaf 3968333667) (.leaf 3851447907))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3738665912) (.branch 17 (.leaf 3629800566) (.leaf 3524675942))) (.branch 20 (.branch 19 (.leaf 3423126474) (.leaf 3324996210)) (.branch 21 (.leaf 3230138115) (.leaf 3138413439)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3049691144) (.leaf 2963847363)) (.branch 25 (.leaf 2880764916) (.leaf 2800332858))) (.branch 28 (.branch 27 (.leaf 2722446063) (.leaf 2647004843)) (.branch 29 (.leaf 2573914593) (.leaf 2503085467)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2434432074) (.branch 32 (.leaf 2367873203) (.leaf 2303331559))) (.branch 35 (.branch 34 (.leaf 2240733527) (.leaf 2180008950)) (.branch 36 (.leaf 2121090921) (.leaf 2063915592)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2008421998) (.leaf 1954551887)) (.branch 40 (.leaf 1902249567) (.leaf 1851461767))) (.branch 43 (.branch 42 (.leaf 1802137494) (.leaf 1754227916)) (.branch 44 (.leaf 1707686242) (.leaf 1662467610))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1618528990) (.branch 47 (.leaf 1575829086) (.leaf 1534328245))) (.branch 50 (.branch 49 (.leaf 1493988377) (.leaf 1454772873)) (.branch 51 (.leaf 1416646532) (.leaf 1379575495)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1343527175) (.leaf 1308470199)) (.branch 55 (.leaf 1274374351) (.leaf 1241210515))) (.branch 58 (.branch 57 (.leaf 1208950628) (.leaf 1177567629)) (.branch 59 (.leaf 1147035414) (.leaf 1117328795))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1088423460) (.branch 62 (.leaf 1060295930) (.leaf 1032923529))) (.branch 65 (.branch 64 (.leaf 1006284349) (.leaf 980357214)) (.branch 66 (.leaf 955121653) (.leaf 930557868)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 906646711) (.leaf 883369655)) (.branch 70 (.leaf 860708769) (.leaf 838646696))) (.branch 73 (.branch 72 (.leaf 817166628) (.leaf 796252290)) (.branch 74 (.leaf 775887915) (.leaf 756058226))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 736748418) (.branch 77 (.leaf 717944143) (.leaf 699631487))) (.branch 80 (.branch 79 (.leaf 681796963) (.leaf 664427486)) (.branch 81 (.leaf 647510368) (.leaf 631033297)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 614984327) (.leaf 599351866)) (.branch 85 (.leaf 584124661) (.leaf 569291788))) (.branch 88 (.branch 87 (.leaf 554842644) (.leaf 540766930)) (.branch 89 (.leaf 527054645) (.leaf 513696078)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 500681791) (.branch 92 (.leaf 488002620) (.leaf 475649659))) (.branch 95 (.branch 94 (.leaf 463614252) (.leaf 451887991)) (.branch 96 (.leaf 440462700) (.leaf 429330436)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 418483475) (.leaf 407914309)) (.branch 100 (.leaf 397615636) (.leaf 387580358))) (.branch 103 (.branch 102 (.leaf 377801573) (.leaf 368272568)) (.branch 104 (.leaf 358986813) (.leaf 349937957))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 341119824) (.leaf 332526404)) (.branch 108 (.leaf 324151851) (.leaf 315990477))) (.branch 111 (.branch 110 (.leaf 308036747) (.leaf 300285277)) (.branch 112 (.leaf 292730827) (.leaf 285368297)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278192724) (.leaf 271199278)) (.branch 116 (.leaf 264383258) (.leaf 257740088))) (.branch 119 (.branch 118 (.leaf 251265315) (.leaf 244954601)) (.branch 120 (.leaf 238803727) (.leaf 232808582)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1174).prefactor = (6200456378680767/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1174).cutoff/(generalMeanRows 1174).c)).2 =
    (247881170916861/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1174).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1174).q*(generalMeanRows 1174).cutoff/2-2 = (1591/544:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable393.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1174).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1174).criticalRate j.val*(generalMeanRows 1174).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1174).c*(generalMeanRows 1174).criticalPoint j.val)).2-
      (generalMeanRows 1174).J/2-(generalMeanRows 1174).error (generalMeanGrid j.val)+
      (generalMeanRows 1174).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1174).c)).2-
      (generalMeanRows 1174).J/2-(generalMeanRows 1174).error 4 := by
  have he : (generalMeanRows 1174).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1174) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1174)
    (generalMeanRows_prefactorDomain 1174) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1174

/-! Kernel-checked entropy margins for general spectral rectangle 1175. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1175
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6034909529) (.branch 2 (.leaf 5856711771) (.leaf 5685593754))) (.branch 5 (.branch 4 (.leaf 5521150780) (.leaf 5363009027)) (.branch 6 (.leaf 5210822690) (.leaf 5064271418)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4923058034) (.leaf 4786906495)) (.branch 10 (.leaf 4655560051) (.leaf 4528779602))) (.branch 13 (.branch 12 (.leaf 4406342212) (.leaf 4288039764)) (.branch 14 (.leaf 4173677755) (.leaf 4063074193))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3956058605) (.branch 17 (.leaf 3852471135) (.leaf 3752161719))) (.branch 20 (.branch 19 (.leaf 3654989339) (.leaf 3560821338)) (.branch 21 (.leaf 3469532805) (.leaf 3381005996)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3295129821) (.leaf 3211799365)) (.branch 25 (.leaf 3130915449) (.leaf 3052384234))) (.branch 28 (.branch 27 (.leaf 2976116845) (.leaf 2902029043)) (.branch 29 (.leaf 2830040902) (.leaf 2760076530)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2692063802) (.branch 32 (.leaf 2625934115) (.leaf 2561622164))) (.branch 35 (.branch 34 (.leaf 2499065733) (.leaf 2438205503)) (.branch 36 (.leaf 2378984871) (.leaf 2321349792)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2265248617) (.leaf 2210631957)) (.branch 40 (.leaf 2157452550) (.leaf 2105665136))) (.branch 43 (.branch 42 (.leaf 2055226348) (.leaf 2006094601)) (.branch 44 (.leaf 1958229997) (.leaf 1911594231))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1866150507) (.branch 47 (.leaf 1821863455) (.leaf 1778699062))) (.branch 50 (.branch 49 (.leaf 1736624595) (.leaf 1695608543)) (.branch 51 (.leaf 1655620551) (.leaf 1616631363)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1578612771) (.leaf 1541537564)) (.branch 55 (.leaf 1505379481) (.leaf 1470113163))) (.branch 58 (.branch 57 (.leaf 1435714117) (.leaf 1402158674)) (.branch 59 (.leaf 1369423953) (.leaf 1337487823))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1306328877) (.branch 62 (.leaf 1275926394) (.leaf 1246260316))) (.branch 65 (.branch 64 (.leaf 1217311214) (.leaf 1189060269)) (.branch 66 (.leaf 1161489242) (.leaf 1134580454)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1108316762) (.leaf 1082681538)) (.branch 70 (.leaf 1057658652) (.leaf 1033232449))) (.branch 73 (.branch 72 (.leaf 1009387735) (.leaf 986109757)) (.branch 74 (.leaf 963384189) (.leaf 941197114))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 919535014) (.branch 77 (.leaf 898384751) (.leaf 877733556))) (.branch 80 (.branch 79 (.leaf 857569016) (.leaf 837879063)) (.branch 81 (.leaf 818651961) (.leaf 799876294)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 781540958) (.leaf 763635150)) (.branch 85 (.leaf 746148356) (.leaf 729070344))) (.branch 88 (.branch 87 (.leaf 712391157) (.leaf 696101099)) (.branch 89 (.leaf 680190730) (.leaf 664650861)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 649472540) (.branch 92 (.leaf 634647049) (.leaf 620165896))) (.branch 95 (.branch 94 (.leaf 606020809) (.leaf 592203729)) (.branch 96 (.leaf 578706802) (.leaf 565522376)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 552642993) (.leaf 540061383)) (.branch 100 (.leaf 527770463) (.leaf 515763325))) (.branch 103 (.branch 102 (.leaf 504033236) (.leaf 492573632)) (.branch 104 (.leaf 481378113) (.leaf 470440436))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 459754517) (.leaf 449314419)) (.branch 108 (.leaf 439114354) (.leaf 429148676))) (.branch 111 (.branch 110 (.leaf 419411877) (.leaf 409898585)) (.branch 112 (.leaf 400603559) (.leaf 391521688)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 382647982) (.leaf 373977575)) (.branch 116 (.leaf 365505718) (.leaf 357227778))) (.branch 119 (.branch 118 (.leaf 349139233) (.leaf 341235672)) (.branch 120 (.leaf 333512787) (.leaf 325966377)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1175).prefactor = (5668193738342571/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1175).cutoff/(generalMeanRows 1175).c)).2 =
    (286576911753613/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1175).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1175).q*(generalMeanRows 1175).c/2-2 = (449/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable336.value]
  have hcontinuation : (generalMeanRows 1175).q*(generalMeanRows 1175).cutoff/2-2 = (201/64:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable395.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1175).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1175).criticalRate j.val*(generalMeanRows 1175).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1175).c*(generalMeanRows 1175).criticalPoint j.val)).2-
      (generalMeanRows 1175).J/2-(generalMeanRows 1175).error (generalMeanGrid j.val)+
      (generalMeanRows 1175).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1175).c)).2-
      (generalMeanRows 1175).J/2-(generalMeanRows 1175).error 4 := by
  have he : (generalMeanRows 1175).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1175) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1175)
    (generalMeanRows_prefactorDomain 1175) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1175

/-! Kernel-checked entropy margins for general spectral rectangle 1176. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1176
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6418234156) (.branch 2 (.leaf 6233186579) (.leaf 6055414661))) (.branch 5 (.branch 4 (.leaf 5884501826) (.leaf 5720063404)) (.branch 6 (.leaf 5561743662) (.leaf 5409213164)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5262166400) (.leaf 5120319680)) (.branch 10 (.leaf 4983409229) (.leaf 4851189485))) (.branch 13 (.branch 12 (.leaf 4723431558) (.leaf 4599921850)) (.branch 14 (.leaf 4480460794) (.leaf 4364861723))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4252949842) (.branch 17 (.leaf 4144561292) (.leaf 4039542298))) (.branch 20 (.branch 19 (.leaf 3937748401) (.leaf 3839043750)) (.branch 21 (.leaf 3743300458) (.leaf 3650398015)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3560222750) (.leaf 3472667340)) (.branch 25 (.leaf 3387630356) (.leaf 3305015850))) (.branch 28 (.branch 27 (.leaf 3224732979) (.leaf 3146695647)) (.branch 29 (.leaf 3070822190) (.leaf 2997035080)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2925260647) (.branch 32 (.leaf 2855428833) (.leaf 2787472956))) (.branch 35 (.branch 34 (.leaf 2721329497) (.leaf 2656937903)) (.branch 36 (.leaf 2594240399) (.leaf 2533181822)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2473709463) (.leaf 2415772919)) (.branch 40 (.leaf 2359323959) (.leaf 2304316398))) (.branch 43 (.branch 42 (.leaf 2250705980) (.leaf 2198450267)) (.branch 44 (.leaf 2147508541) (.leaf 2097841710))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2049412215) (.branch 47 (.leaf 2002183954) (.leaf 1956122202))) (.branch 50 (.branch 49 (.leaf 1911193541) (.leaf 1867365790)) (.branch 51 (.leaf 1824607949) (.leaf 1782890133)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1742183523) (.leaf 1702460312)) (.branch 55 (.leaf 1663693657) (.leaf 1625857633))) (.branch 58 (.branch 57 (.leaf 1588927194) (.leaf 1552878128)) (.branch 59 (.leaf 1517687023) (.leaf 1483331230))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1449788833) (.branch 62 (.leaf 1417038611) (.leaf 1385060014))) (.branch 65 (.branch 64 (.leaf 1353833135) (.leaf 1323338678)) (.branch 66 (.leaf 1293557941) (.leaf 1264472784)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1236065615) (.leaf 1208319362)) (.branch 70 (.leaf 1181217456) (.leaf 1154743811))) (.branch 73 (.branch 72 (.leaf 1128882807) (.leaf 1103619271)) (.branch 74 (.leaf 1078938464) (.leaf 1054826062))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1031268140) (.branch 77 (.leaf 1008251163) (.leaf 985761970))) (.branch 80 (.branch 79 (.leaf 963787759) (.leaf 942316077)) (.branch 81 (.leaf 921334809) (.leaf 900832166)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 880796672) (.leaf 861217158)) (.branch 85 (.leaf 842082749) (.leaf 823382856))) (.branch 88 (.branch 87 (.leaf 805107166) (.leaf 787245636)) (.branch 89 (.leaf 769788480) (.leaf 752726165)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 736049404) (.branch 92 (.leaf 719749143) (.leaf 703816562))) (.branch 95 (.branch 94 (.leaf 688243062) (.leaf 673020259)) (.branch 96 (.leaf 658139982) (.leaf 643594262)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 629375329) (.leaf 615475607)) (.branch 100 (.leaf 601887705) (.leaf 588604416))) (.branch 103 (.branch 102 (.leaf 575618708) (.leaf 562923722)) (.branch 104 (.leaf 550512766) (.leaf 538379312))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 526516989) (.leaf 514919580)) (.branch 108 (.leaf 503581019) (.leaf 492495384))) (.branch 111 (.branch 110 (.leaf 481656898) (.leaf 471059920)) (.branch 112 (.leaf 460698945) (.leaf 450568598)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 440663632) (.leaf 430978925)) (.branch 116 (.leaf 421509477) (.leaf 412250405))) (.branch 119 (.branch 118 (.leaf 403196940) (.leaf 394344428)) (.branch 120 (.leaf 385688323) (.leaf 377224184)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1176).prefactor = (1172121681201799/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1176).cutoff/(generalMeanRows 1176).c)).2 =
    (116572527526837/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1176).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1176).q*(generalMeanRows 1176).c/2-2 = (87/100:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable246.value]
  have hcontinuation : (generalMeanRows 1176).q*(generalMeanRows 1176).cutoff/2-2 = (201/64:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable395.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1176).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1176).criticalRate j.val*(generalMeanRows 1176).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1176).c*(generalMeanRows 1176).criticalPoint j.val)).2-
      (generalMeanRows 1176).J/2-(generalMeanRows 1176).error (generalMeanGrid j.val)+
      (generalMeanRows 1176).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1176).c)).2-
      (generalMeanRows 1176).J/2-(generalMeanRows 1176).error 4 := by
  have he : (generalMeanRows 1176).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1176) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1176)
    (generalMeanRows_prefactorDomain 1176) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1176

/-! Kernel-checked entropy margins for general spectral rectangle 1177. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1177
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6139878533) (.branch 2 (.leaf 5971899352) (.leaf 5810426997))) (.branch 5 (.branch 4 (.leaf 5655091247) (.leaf 5505549758)) (.branch 6 (.leaf 5361485511) (.leaf 5222604543)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5088633909) (.leaf 4959319862)) (.branch 10 (.leaf 4834426215) (.leaf 4713732871))) (.branch 13 (.branch 12 (.leaf 4597034489) (.leaf 4484139290)) (.branch 14 (.leaf 4374867961) (.leaf 4269052676))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4166536200) (.branch 17 (.leaf 4067171068) (.leaf 3970818849))) (.branch 20 (.branch 19 (.leaf 3877349466) (.leaf 3786640576)) (.branch 21 (.leaf 3698577007) (.leaf 3613050236)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3529957917) (.leaf 3449203444)) (.branch 25 (.leaf 3370695548) (.leaf 3294347934))) (.branch 28 (.branch 27 (.leaf 3220078933) (.leaf 3147811200)) (.branch 29 (.leaf 3077471417) (.leaf 3008990032)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2942301012) (.branch 32 (.leaf 2877341614) (.leaf 2814052179))) (.branch 35 (.branch 34 (.leaf 2752375932) (.leaf 2692258808)) (.branch 36 (.leaf 2633649279) (.leaf 2576498202)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2520758676) (.leaf 2466385904)) (.branch 40 (.leaf 2413337075) (.leaf 2361571241))) (.branch 43 (.branch 42 (.leaf 2311049214) (.leaf 2261733467)) (.branch 44 (.leaf 2213588034) (.leaf 2166578431))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2120671568) (.branch 47 (.leaf 2075835676) (.leaf 2032040236))) (.branch 50 (.branch 49 (.leaf 1989255911) (.leaf 1947454487)) (.branch 51 (.leaf 1906608813) (.leaf 1866692744)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1827681094) (.leaf 1789549590)) (.branch 55 (.leaf 1752274818) (.leaf 1715834193))) (.branch 58 (.branch 57 (.leaf 1680205909) (.leaf 1645368908)) (.branch 59 (.leaf 1611302844) (.leaf 1577988048))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1545405499) (.branch 62 (.leaf 1513536796) (.leaf 1482364127))) (.branch 65 (.branch 64 (.leaf 1451870245) (.leaf 1422038445)) (.branch 66 (.leaf 1392852539) (.leaf 1364296835)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1336356115) (.leaf 1309015618)) (.branch 70 (.leaf 1282261021) (.leaf 1256078418))) (.branch 73 (.branch 72 (.leaf 1230454309) (.leaf 1205375581)) (.branch 74 (.leaf 1180829492) (.leaf 1156803661))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1133286050) (.branch 77 (.leaf 1110264956) (.leaf 1087728993))) (.branch 80 (.branch 79 (.leaf 1065667088) (.leaf 1044068462)) (.branch 81 (.leaf 1022922626) (.leaf 1002219366)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 981948739) (.leaf 962101059)) (.branch 85 (.leaf 942666889) (.leaf 923637037))) (.branch 88 (.branch 87 (.leaf 905002543) (.leaf 886754675)) (.branch 89 (.leaf 868884918) (.leaf 851384972)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 834246740) (.branch 92 (.leaf 817462327) (.leaf 801024031))) (.branch 95 (.branch 94 (.leaf 784924335) (.leaf 769155907)) (.branch 96 (.leaf 753711589) (.leaf 738584397)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 723767510) (.leaf 709254271)) (.branch 100 (.leaf 695038179) (.leaf 681112887))) (.branch 103 (.branch 102 (.leaf 667472193) (.leaf 654110043)) (.branch 104 (.leaf 641020520) (.leaf 628197846))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 615636373) (.leaf 603330585)) (.branch 108 (.leaf 591275088) (.leaf 579464615))) (.branch 111 (.branch 110 (.leaf 567894014) (.leaf 556558250)) (.branch 112 (.leaf 545452404) (.leaf 534571663)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 523911325) (.leaf 513466788)) (.branch 116 (.leaf 503233557) (.leaf 493207233))) (.branch 119 (.branch 118 (.leaf 483383516) (.leaf 473758199)) (.branch 120 (.leaf 464327168) (.leaf 455086399)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1177).prefactor = (4007043095747/781250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1177).cutoff/(generalMeanRows 1177).c)).2 =
    (138545857248693/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1177).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1177).q*(generalMeanRows 1177).c/2-2 = (6287/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable394.value]
  have hcontinuation : (generalMeanRows 1177).q*(generalMeanRows 1177).cutoff/2-2 = (3148/1105:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable396.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1177).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1177).criticalRate j.val*(generalMeanRows 1177).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1177).c*(generalMeanRows 1177).criticalPoint j.val)).2-
      (generalMeanRows 1177).J/2-(generalMeanRows 1177).error (generalMeanGrid j.val)+
      (generalMeanRows 1177).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1177).c)).2-
      (generalMeanRows 1177).J/2-(generalMeanRows 1177).error 4 := by
  have he : (generalMeanRows 1177).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1177) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1177)
    (generalMeanRows_prefactorDomain 1177) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1177

/-! Kernel-checked entropy margins for general spectral rectangle 1178. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1178
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6236087787) (.branch 2 (.leaf 6061054566) (.leaf 5892864867))) (.branch 5 (.branch 4 (.leaf 5731130362) (.leaf 5575491860)) (.branch 6 (.leaf 5425616639) (.leaf 5281196079)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5141943534) (.leaf 5007592436)) (.branch 10 (.leaf 4877894585) (.leaf 4752618609))) (.branch 13 (.branch 12 (.leaf 4631548583) (.leaf 4514482766)) (.branch 14 (.leaf 4401232477) (.leaf 4291621057))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4185482938) (.branch 17 (.leaf 4082662790) (.leaf 3983014747))) (.branch 20 (.branch 19 (.leaf 3886401699) (.leaf 3792694648)) (.branch 21 (.leaf 3701772110) (.leaf 3613519582)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3527829040) (.leaf 3444598484)) (.branch 25 (.leaf 3363731522) (.leaf 3285136981))) (.branch 28 (.branch 27 (.leaf 3208728555) (.leaf 3134424476)) (.branch 29 (.leaf 3062147217) (.leaf 2991823207)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2923382581) (.branch 32 (.leaf 2856758936) (.leaf 2791889118))) (.branch 35 (.branch 34 (.leaf 2728713010) (.leaf 2667173350)) (.branch 36 (.leaf 2607215554) (.leaf 2548787552)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2491839639) (.leaf 2436324332)) (.branch 40 (.leaf 2382196245) (.leaf 2329411962))) (.branch 43 (.branch 42 (.leaf 2277929926) (.leaf 2227710335)) (.branch 44 (.leaf 2178715044) (.leaf 2130907468))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2084252507) (.branch 47 (.leaf 2038716454) (.leaf 1994266929))) (.branch 50 (.branch 49 (.leaf 1950872808) (.leaf 1908504154)) (.branch 51 (.leaf 1867132159) (.leaf 1826729084)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1787268211) (.leaf 1748723785)) (.branch 55 (.leaf 1711070973) (.leaf 1674285815))) (.branch 58 (.branch 57 (.leaf 1638345187) (.leaf 1603226756)) (.branch 59 (.leaf 1568908949) (.leaf 1535370915))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1502592491) (.branch 62 (.leaf 1470554177) (.leaf 1439237098))) (.branch 65 (.branch 64 (.leaf 1408622987) (.leaf 1378694149)) (.branch 66 (.leaf 1349433444) (.leaf 1320824261)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1292850496) (.leaf 1265496531)) (.branch 70 (.leaf 1238747215) (.leaf 1212587848))) (.branch 73 (.branch 72 (.leaf 1187004157) (.leaf 1161982288)) (.branch 74 (.leaf 1137508780) (.leaf 1113570561))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1090154924) (.branch 77 (.leaf 1067249519) (.leaf 1044842339))) (.branch 80 (.branch 79 (.leaf 1022921707) (.leaf 1001476265)) (.branch 81 (.leaf 980494962) (.leaf 959967043)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 939882041) (.leaf 920229767)) (.branch 85 (.leaf 901000296) (.leaf 882183966))) (.branch 88 (.branch 87 (.leaf 863771362) (.leaf 845753315)) (.branch 89 (.leaf 828120887) (.leaf 810865369)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 793978272) (.branch 92 (.leaf 777451320) (.leaf 761276443))) (.branch 95 (.branch 94 (.leaf 745445772) (.leaf 729951633)) (.branch 96 (.leaf 714786540) (.leaf 699943191)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 685414459) (.leaf 671193392)) (.branch 100 (.leaf 657273205) (.leaf 643647275))) (.branch 103 (.branch 102 (.leaf 630309139) (.leaf 617252487)) (.branch 104 (.leaf 604471156) (.leaf 591959133))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 579710543) (.leaf 567719650)) (.branch 108 (.leaf 555980851) (.leaf 544488674))) (.branch 111 (.branch 110 (.leaf 533237773) (.leaf 522222927)) (.branch 112 (.leaf 511439034) (.leaf 500881109)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 490544282) (.leaf 480423794)) (.branch 116 (.leaf 470514993) (.leaf 460813335))) (.branch 119 (.branch 118 (.leaf 451314376) (.leaf 442013774)) (.branch 120 (.leaf 432907285) (.leaf 423990759)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1178).prefactor = (2679662742636501/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1178).cutoff/(generalMeanRows 1178).c)).2 =
    (544005224079017/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1178).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1178).q*(generalMeanRows 1178).c/2-2 = (1303/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable271.value]
  have hcontinuation : (generalMeanRows 1178).q*(generalMeanRows 1178).cutoff/2-2 = (3148/1105:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable396.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1178).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1178).criticalRate j.val*(generalMeanRows 1178).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1178).c*(generalMeanRows 1178).criticalPoint j.val)).2-
      (generalMeanRows 1178).J/2-(generalMeanRows 1178).error (generalMeanGrid j.val)+
      (generalMeanRows 1178).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1178).c)).2-
      (generalMeanRows 1178).J/2-(generalMeanRows 1178).error 4 := by
  have he : (generalMeanRows 1178).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1178) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1178)
    (generalMeanRows_prefactorDomain 1178) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1178

/-! Kernel-checked entropy margins for general spectral rectangle 1179. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1179
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6424482536) (.branch 2 (.leaf 6241885559) (.leaf 6066461937))) (.branch 5 (.branch 4 (.leaf 5897805110) (.leaf 5735538963)) (.branch 6 (.leaf 5579315046) (.leaf 5428810101)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5283723841) (.leaf 5143776968)) (.branch 10 (.leaf 5008709385) (.leaf 4878278597))) (.branch 13 (.branch 12 (.leaf 4752258255) (.leaf 4630436851)) (.branch 14 (.leaf 4512616533) (.leaf 4398612026))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4288249660) (.branch 17 (.leaf 4181366476) (.leaf 4077809419))) (.branch 20 (.branch 19 (.leaf 3977434599) (.leaf 3880106616)) (.branch 21 (.leaf 3785697939) (.leaf 3694088345)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3605164395) (.leaf 3518818964)) (.branch 25 (.leaf 3434950795) (.leaf 3353464105))) (.branch 28 (.branch 27 (.leaf 3274268210) (.leaf 3197277181)) (.branch 29 (.leaf 3122409535) (.leaf 3049587939)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2978738943) (.branch 32 (.leaf 2909792732) (.leaf 2842682895))) (.branch 35 (.branch 34 (.leaf 2777346213) (.leaf 2713722460)) (.branch 36 (.leaf 2651754221) (.leaf 2591386722)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2532567671) (.leaf 2475247113)) (.branch 40 (.leaf 2419377292) (.leaf 2364912524))) (.branch 43 (.branch 42 (.leaf 2311809080) (.leaf 2260025075)) (.branch 44 (.leaf 2209520363) (.leaf 2160256445))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2112196378) (.branch 47 (.leaf 2065304690) (.leaf 2019547303))) (.branch 50 (.branch 49 (.leaf 1974891457) (.leaf 1931305649)) (.branch 51 (.leaf 1888759559) (.leaf 1847223998)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1806670846) (.leaf 1767073004)) (.branch 55 (.leaf 1728404340) (.leaf 1690639646))) (.branch 58 (.branch 57 (.leaf 1653754591) (.leaf 1617725682)) (.branch 59 (.leaf 1582530225) (.leaf 1548146289))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1514552668) (.branch 62 (.leaf 1481728853) (.leaf 1449655002))) (.branch 65 (.branch 64 (.leaf 1418311904) (.leaf 1387680962)) (.branch 66 (.leaf 1357744158) (.leaf 1328484036)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1299883672) (.leaf 1271926659)) (.branch 70 (.leaf 1244597083) (.leaf 1217879501))) (.branch 73 (.branch 72 (.leaf 1191758929) (.leaf 1166220817)) (.branch 74 (.leaf 1141251039) (.leaf 1116835873))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1092961986) (.branch 77 (.leaf 1069616422) (.leaf 1046786586))) (.branch 80 (.branch 79 (.leaf 1024460232) (.leaf 1002625453)) (.branch 81 (.leaf 981270663) (.leaf 960384593)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 939956276) (.leaf 919975036)) (.branch 85 (.leaf 900430482) (.leaf 881312495))) (.branch 88 (.branch 87 (.leaf 862611222) (.leaf 844317065)) (.branch 89 (.leaf 826420674) (.leaf 808912939)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 791784982) (.branch 92 (.leaf 775028151) (.leaf 758634012))) (.branch 95 (.branch 94 (.leaf 742594342) (.leaf 726901125)) (.branch 96 (.leaf 711546542) (.leaf 696522968)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 681822965) (.leaf 667439280)) (.branch 100 (.leaf 653364832) (.leaf 639592716))) (.branch 103 (.branch 102 (.leaf 626116191) (.leaf 612928681)) (.branch 104 (.leaf 600023765) (.leaf 587395177))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 575036800) (.leaf 562942660)) (.branch 108 (.leaf 551106927) (.leaf 539523906))) (.branch 111 (.branch 110 (.leaf 528188038) (.leaf 517093891)) (.branch 112 (.leaf 506236162) (.leaf 495609670)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 485209355) (.leaf 475030275)) (.branch 116 (.leaf 465067598) (.leaf 455316607))) (.branch 119 (.branch 118 (.leaf 445772693) (.leaf 436431349)) (.branch 120 (.leaf 427288174) (.leaf 418338866)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1179).prefactor = (1119995505834387/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1179).cutoff/(generalMeanRows 1179).c)).2 =
    (538954708292947/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1179).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1179).q*(generalMeanRows 1179).c/2-2 = (6629/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable392.value]
  have hcontinuation : (generalMeanRows 1179).q*(generalMeanRows 1179).cutoff/2-2 = (3148/1105:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable396.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1179).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1179).criticalRate j.val*(generalMeanRows 1179).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1179).c*(generalMeanRows 1179).criticalPoint j.val)).2-
      (generalMeanRows 1179).J/2-(generalMeanRows 1179).error (generalMeanGrid j.val)+
      (generalMeanRows 1179).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1179).c)).2-
      (generalMeanRows 1179).J/2-(generalMeanRows 1179).error 4 := by
  have he : (generalMeanRows 1179).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1179) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1179)
    (generalMeanRows_prefactorDomain 1179) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1179

/-! Kernel-checked entropy margins for general spectral rectangle 1180. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1180
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6525852100) (.branch 2 (.leaf 6335754148) (.leaf 6153197196))) (.branch 5 (.branch 4 (.leaf 5977754712) (.leaf 5809031990)) (.branch 6 (.leaf 5646663249) (.leaf 5490309051)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5339653984) (.leaf 5194404591)) (.branch 10 (.leaf 5054287510) (.leaf 4919047793))) (.branch 13 (.branch 12 (.leaf 4788447398) (.leaf 4662263819)) (.branch 14 (.leaf 4540288851) (.leaf 4422327465))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4308196786) (.branch 17 (.leaf 4197725171) (.leaf 4090751355))) (.branch 20 (.branch 19 (.leaf 3987123684) (.leaf 3886699408)) (.branch 21 (.leaf 3789344035) (.leaf 3694930741)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3603339826) (.leaf 3514458217)) (.branch 25 (.leaf 3428179010) (.leaf 3344401050))) (.branch 28 (.branch 27 (.leaf 3263028542) (.leaf 3183970693)) (.branch 29 (.leaf 3107141387) (.leaf 3032458872)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2959845488) (.branch 32 (.leaf 2889227400) (.leaf 2820534360))) (.branch 35 (.branch 34 (.leaf 2753699483) (.leaf 2688659042)) (.branch 36 (.leaf 2625352274) (.leaf 2563721199)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2503710463) (.leaf 2445267175)) (.branch 40 (.leaf 2388340769) (.leaf 2332882868))) (.branch 43 (.branch 42 (.leaf 2278847164) (.leaf 2226189295)) (.branch 44 (.leaf 2174866745) (.leaf 2124838736))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2076066141) (.branch 47 (.leaf 2028511389) (.leaf 1982138388))) (.branch 50 (.branch 49 (.leaf 1936912444) (.leaf 1892800193)) (.branch 51 (.leaf 1849769531) (.leaf 1807789548)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1766830477) (.leaf 1726863627)) (.branch 55 (.leaf 1687861341) (.leaf 1649796941))) (.branch 58 (.branch 57 (.leaf 1612644681) (.leaf 1576379710)) (.branch 59 (.leaf 1540978023) (.leaf 1506416426))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1472672503) (.branch 62 (.leaf 1439724574) (.leaf 1407551672))) (.branch 65 (.branch 64 (.leaf 1376133503) (.leaf 1345450423)) (.branch 66 (.leaf 1315483412) (.leaf 1286214042)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1257624457) (.leaf 1229697351)) (.branch 70 (.leaf 1202415943) (.leaf 1175763955))) (.branch 73 (.branch 72 (.leaf 1149725598) (.leaf 1124285548)) (.branch 74 (.leaf 1099428931) (.leaf 1075141305))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1051408644) (.branch 77 (.leaf 1028217322) (.leaf 1005554102))) (.branch 80 (.branch 79 (.leaf 983406116) (.leaf 961760858)) (.branch 81 (.leaf 940606168) (.leaf 919930220)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 899721512) (.leaf 879968854)) (.branch 85 (.leaf 860661358) (.leaf 841788426))) (.branch 88 (.branch 87 (.leaf 823339745) (.leaf 805305274)) (.branch 89 (.leaf 787675235) (.leaf 770440108)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 753590618) (.branch 92 (.leaf 737117732) (.leaf 721012649))) (.branch 95 (.branch 94 (.leaf 705266795) (.leaf 689871812)) (.branch 96 (.leaf 674819554) (.leaf 660102084)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 645711662) (.leaf 631640741)) (.branch 100 (.leaf 617881963) (.leaf 604428155))) (.branch 103 (.branch 102 (.leaf 591272317) (.leaf 578407625)) (.branch 104 (.leaf 565827421) (.leaf 553525209))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 541494653) (.leaf 529729570)) (.branch 108 (.leaf 518223926) (.leaf 506971834))) (.branch 111 (.branch 110 (.leaf 495967548) (.leaf 485205459)) (.branch 112 (.leaf 474680092) (.leaf 464386105)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 454318280) (.leaf 444471525)) (.branch 116 (.leaf 434840866) (.leaf 425421449))) (.branch 119 (.branch 118 (.leaf 416208533) (.leaf 407197488)) (.branch 120 (.leaf 398383794) (.leaf 389763034)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1180).prefactor = (1462858918226029/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1180).cutoff/(generalMeanRows 1180).c)).2 =
    (52892956167357/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1180).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1180).q*(generalMeanRows 1180).cutoff/2-2 = (3148/1105:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable396.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1180).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1180).criticalRate j.val*(generalMeanRows 1180).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1180).c*(generalMeanRows 1180).criticalPoint j.val)).2-
      (generalMeanRows 1180).J/2-(generalMeanRows 1180).error (generalMeanGrid j.val)+
      (generalMeanRows 1180).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1180).c)).2-
      (generalMeanRows 1180).J/2-(generalMeanRows 1180).error 4 := by
  have he : (generalMeanRows 1180).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1180) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1180)
    (generalMeanRows_prefactorDomain 1180) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1180

/-! Kernel-checked entropy margins for general spectral rectangle 1181. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1181
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6723362940) (.branch 2 (.leaf 6525133725) (.leaf 6334807080))) (.branch 5 (.branch 4 (.leaf 6151936398) (.leaf 5976108340)) (.branch 6 (.leaf 5806939802) (.leaf 5644075219)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5487184143) (.leaf 5335959083)) (.branch 10 (.leaf 5190113560) (.leaf 5049380356))) (.branch 13 (.branch 12 (.leaf 4913509931) (.leaf 4782269000)) (.branch 14 (.leaf 4655439235) (.leaf 4532816098))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4414207768) (.branch 17 (.leaf 4299434176) (.leaf 4188326120))) (.branch 20 (.branch 19 (.leaf 4080724456) (.leaf 3976479365)) (.branch 21 (.leaf 3875449674) (.leaf 3777502239)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3682511382) (.leaf 3590358365)) (.branch 25 (.leaf 3500930913) (.leaf 3414122779))) (.branch 28 (.branch 27 (.leaf 3329833332) (.leaf 3247967186)) (.branch 29 (.leaf 3168433855) (.leaf 3091147436)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3016026313) (.branch 32 (.leaf 2942992884) (.leaf 2871973313))) (.branch 35 (.branch 34 (.leaf 2802897290) (.leaf 2735697822)) (.branch 36 (.leaf 2670311026) (.leaf 2606675944)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2544734374) (.leaf 2484430702)) (.branch 40 (.leaf 2425711756) (.leaf 2368526667))) (.branch 43 (.branch 42 (.leaf 2312826737) (.leaf 2258565316)) (.branch 44 (.leaf 2205697695) (.leaf 2154180993))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2103974063) (.branch 47 (.leaf 2055037400) (.leaf 2007333050))) (.branch 50 (.branch 49 (.leaf 1960824535) (.leaf 1915476773)) (.branch 51 (.leaf 1871256011) (.leaf 1828129754)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1786066707) (.leaf 1745036713)) (.branch 55 (.leaf 1705010702) (.leaf 1665960634))) (.branch 58 (.branch 57 (.leaf 1627859456) (.leaf 1590681052)) (.branch 59 (.leaf 1554400202) (.leaf 1518992542))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1484434524) (.branch 62 (.leaf 1450703381) (.leaf 1417777092))) (.branch 65 (.branch 64 (.leaf 1385634352) (.leaf 1354254538)) (.branch 66 (.leaf 1323617686) (.leaf 1293704458)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1264496117) (.leaf 1235974508)) (.branch 70 (.leaf 1208122028) (.leaf 1180921609))) (.branch 73 (.branch 72 (.leaf 1154356695) (.leaf 1128411223)) (.branch 74 (.leaf 1103069603) (.leaf 1078316702))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1054137827) (.branch 77 (.leaf 1030518705) (.leaf 1007445475))) (.branch 80 (.branch 79 (.leaf 984904666) (.leaf 962883188)) (.branch 81 (.leaf 941368315) (.leaf 920347676)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 899809240) (.leaf 879741306)) (.branch 85 (.leaf 860132491) (.leaf 840971720))) (.branch 88 (.branch 87 (.leaf 822248216) (.leaf 803951489)) (.branch 89 (.leaf 786071329) (.leaf 768597795)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 751521208) (.branch 92 (.leaf 734832141) (.leaf 718521412))) (.branch 95 (.branch 94 (.leaf 702580078) (.leaf 686999426)) (.branch 96 (.leaf 671770966) (.leaf 656886424)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 642337739) (.leaf 628117050)) (.branch 100 (.leaf 614216698) (.leaf 600629214))) (.branch 103 (.branch 102 (.leaf 587347317) (.leaf 574363905)) (.branch 104 (.leaf 561672057) (.leaf 549265018))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 537136203) (.leaf 525279187)) (.branch 108 (.leaf 513687704) (.leaf 502355640))) (.branch 111 (.branch 110 (.leaf 491277029) (.leaf 480446052)) (.branch 112 (.leaf 469857030) (.leaf 459504419)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449382812) (.leaf 439486930)) (.branch 116 (.leaf 429811620) (.leaf 420351854))) (.branch 119 (.branch 118 (.leaf 411102721) (.leaf 402059430)) (.branch 120 (.leaf 393217301) (.leaf 384571767)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1181).prefactor = (6114185147310377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1181).cutoff/(generalMeanRows 1181).c)).2 =
    (104790885406691/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1181).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1181).q*(generalMeanRows 1181).cutoff/2-2 = (3148/1105:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable396.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1181).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1181).criticalRate j.val*(generalMeanRows 1181).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1181).c*(generalMeanRows 1181).criticalPoint j.val)).2-
      (generalMeanRows 1181).J/2-(generalMeanRows 1181).error (generalMeanGrid j.val)+
      (generalMeanRows 1181).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1181).c)).2-
      (generalMeanRows 1181).J/2-(generalMeanRows 1181).error 4 := by
  have he : (generalMeanRows 1181).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1181) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1181)
    (generalMeanRows_prefactorDomain 1181) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1181

/-! Kernel-checked entropy margins for general spectral rectangle 1182. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1182
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6391587949) (.branch 2 (.leaf 6215490832) (.leaf 6046189487))) (.branch 5 (.branch 4 (.leaf 5883295100) (.leaf 5726448619)) (.branch 6 (.leaf 5575317995) (.leaf 5429595715)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5288996610) (.leaf 5153255881)) (.branch 10 (.leaf 5022127334) (.leaf 4895381791))) (.branch 13 (.branch 12 (.leaf 4772805658) (.leaf 4654199634)) (.branch 14 (.leaf 4539377540) (.leaf 4428165263))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4320399795) (.branch 17 (.leaf 4215928361) (.leaf 4114607627))) (.branch 20 (.branch 19 (.leaf 4016302975) (.leaf 3920887847)) (.branch 21 (.leaf 3828243141) (.leaf 3738256664)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3650822625) (.leaf 3565841177)) (.branch 25 (.leaf 3483217992) (.leaf 3402863877))) (.branch 28 (.branch 27 (.leaf 3324694412) (.leaf 3248629626)) (.branch 29 (.leaf 3174593695) (.leaf 3102514662)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3032324183) (.branch 32 (.leaf 2963957291) (.leaf 2897352173))) (.branch 35 (.branch 34 (.leaf 2832449977) (.leaf 2769194615)) (.branch 36 (.leaf 2707532599) (.leaf 2647412876)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2588786685) (.leaf 2531607411)) (.branch 40 (.leaf 2475830466) (.leaf 2421413167))) (.branch 43 (.branch 42 (.leaf 2368314625) (.leaf 2316495645)) (.branch 44 (.leaf 2265918627) (.leaf 2216547483))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2168347547) (.branch 47 (.leaf 2121285505) (.leaf 2075329318))) (.branch 50 (.branch 49 (.leaf 2030448157) (.leaf 1986612342)) (.branch 51 (.leaf 1943793276) (.leaf 1901963401)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1861096138) (.leaf 1821165839)) (.branch 55 (.leaf 1782147750) (.leaf 1744017959))) (.branch 58 (.branch 57 (.leaf 1706753360) (.leaf 1670331619)) (.branch 59 (.leaf 1634731134) (.leaf 1599931001))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1565910991) (.branch 62 (.leaf 1532651511) (.leaf 1500133581))) (.branch 65 (.branch 64 (.leaf 1468338811) (.leaf 1437249369)) (.branch 66 (.leaf 1406847964) (.leaf 1377117820)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1348042661) (.leaf 1319606682)) (.branch 70 (.leaf 1291794540) (.leaf 1264591331))) (.branch 73 (.branch 72 (.leaf 1237982573) (.leaf 1211954195)) (.branch 74 (.leaf 1186492515) (.leaf 1161584230))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1137216404) (.branch 77 (.leaf 1113376450) (.leaf 1090052121))) (.branch 80 (.branch 79 (.leaf 1067231499) (.leaf 1044902980)) (.branch 81 (.leaf 1023055267) (.leaf 1001677358)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 980758538) (.leaf 960288367)) (.branch 85 (.leaf 940256673) (.leaf 920653543))) (.branch 88 (.branch 87 (.leaf 901469315) (.leaf 882694570)) (.branch 89 (.leaf 864320124) (.leaf 846337022)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 828736530) (.branch 92 (.leaf 811510129) (.leaf 794649509))) (.branch 95 (.branch 94 (.leaf 778146561) (.leaf 761993374)) (.branch 96 (.leaf 746182228) (.leaf 730705586)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 715556093) (.leaf 700726571)) (.branch 100 (.leaf 686210007) (.leaf 671999559))) (.branch 103 (.branch 102 (.leaf 658088542) (.leaf 644470431)) (.branch 104 (.leaf 631138850) (.leaf 618087574))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 605310522) (.leaf 592801751)) (.branch 108 (.leaf 580555459) (.leaf 568565974))) (.branch 111 (.branch 110 (.leaf 556827756) (.leaf 545335390)) (.branch 112 (.leaf 534083586) (.leaf 523067171)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 512281094) (.leaf 501720413)) (.branch 116 (.leaf 491380302) (.leaf 481256040))) (.branch 119 (.branch 118 (.leaf 471343014) (.leaf 461636713)) (.branch 120 (.leaf 452132728) (.leaf 442826746)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1182).prefactor = (219661513722051/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1182).cutoff/(generalMeanRows 1182).c)).2 =
    (11741270443551/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1182).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1182).q*(generalMeanRows 1182).cutoff/2-2 = (199/65:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable397.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1182).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1182).criticalRate j.val*(generalMeanRows 1182).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1182).c*(generalMeanRows 1182).criticalPoint j.val)).2-
      (generalMeanRows 1182).J/2-(generalMeanRows 1182).error (generalMeanGrid j.val)+
      (generalMeanRows 1182).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1182).c)).2-
      (generalMeanRows 1182).J/2-(generalMeanRows 1182).error 4 := by
  have he : (generalMeanRows 1182).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1182) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1182)
    (generalMeanRows_prefactorDomain 1182) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1182

/-! Kernel-checked entropy margins for general spectral rectangle 1183. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1183
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6549911078) (.branch 2 (.leaf 6367169963) (.leaf 6191515749))) (.branch 5 (.branch 4 (.leaf 6022543485) (.leaf 5859879160)) (.branch 6 (.leaf 5703176830) (.leaf 5552116066)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5406399667) (.leaf 5265751614)) (.branch 10 (.leaf 5129915239) (.leaf 4998651572))) (.branch 13 (.branch 12 (.leaf 4871737853) (.leaf 4748966190)) (.branch 14 (.leaf 4630142347) (.leaf 4515084642))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4403622950) (.branch 17 (.leaf 4295597798) (.leaf 4190859542))) (.branch 20 (.branch 19 (.leaf 4089267612) (.leaf 3990689830)) (.branch 21 (.leaf 3895001788) (.leaf 3802086270)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3711832732) (.leaf 3624136825)) (.branch 25 (.leaf 3538899951) (.leaf 3456028864))) (.branch 28 (.branch 27 (.leaf 3375435297) (.leaf 3297035620)) (.branch 29 (.leaf 3220750529) (.leaf 3146504755)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3074226800) (.branch 32 (.leaf 3003848687) (.leaf 2935305735))) (.branch 35 (.branch 34 (.leaf 2868536352) (.leaf 2803481835)) (.branch 36 (.leaf 2740086196) (.leaf 2678295990)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2618060168) (.leaf 2559329925)) (.branch 40 (.leaf 2502058575) (.leaf 2446201422))) (.branch 43 (.branch 42 (.leaf 2391715650) (.leaf 2338560213)) (.branch 44 (.leaf 2286695735) (.leaf 2236084421))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2186689968) (.branch 47 (.leaf 2138477487) (.leaf 2091413424))) (.branch 50 (.branch 49 (.leaf 2045465493) (.leaf 2000602611)) (.branch 51 (.leaf 1956794834) (.leaf 1914013301)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1872230183) (.leaf 1831418626)) (.branch 55 (.leaf 1791552711) (.leaf 1752607405))) (.branch 58 (.branch 57 (.leaf 1714558522) (.leaf 1677382682)) (.branch 59 (.leaf 1641057277) (.leaf 1605560431))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1570870976) (.branch 62 (.leaf 1536968411) (.leaf 1503832884))) (.branch 65 (.branch 64 (.leaf 1471445154) (.leaf 1439786575)) (.branch 66 (.leaf 1408839064) (.leaf 1378585082)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1349007612) (.leaf 1320090138)) (.branch 70 (.leaf 1291816623) (.leaf 1264171496))) (.branch 73 (.branch 72 (.leaf 1237139628) (.leaf 1210706322)) (.branch 74 (.leaf 1184857290) (.leaf 1159578644))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1134856879) (.branch 77 (.leaf 1110678860) (.leaf 1087031808))) (.branch 80 (.branch 79 (.leaf 1063903289) (.leaf 1041281202)) (.branch 81 (.leaf 1019153767) (.leaf 997509514)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 976337274) (.leaf 955626169)) (.branch 85 (.leaf 935365603) (.leaf 915545251))) (.branch 88 (.branch 87 (.leaf 896155051) (.leaf 877185198)) (.branch 89 (.leaf 858626134) (.leaf 840468542)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 822703335) (.branch 92 (.leaf 805321656) (.leaf 788314863))) (.branch 95 (.branch 94 (.leaf 771674528) (.leaf 755392430)) (.branch 96 (.leaf 739460549) (.leaf 723871058)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 708616320) (.leaf 693688882)) (.branch 100 (.leaf 679081469) (.leaf 664786981))) (.branch 103 (.branch 102 (.leaf 650798487) (.leaf 637109217)) (.branch 104 (.leaf 623712567) (.leaf 610602082))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 597771463) (.leaf 585214558)) (.branch 108 (.leaf 572925355) (.leaf 560897987))) (.branch 111 (.branch 110 (.leaf 549126718) (.leaf 537605948)) (.branch 112 (.leaf 526330206) (.leaf 515294145)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 504492541) (.leaf 493920292)) (.branch 116 (.leaf 483572409) (.leaf 473444019))) (.branch 119 (.branch 118 (.leaf 463530359) (.leaf 453826775)) (.branch 120 (.leaf 444328717) (.leaf 435031737)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1183).prefactor = (114151389203289/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1183).cutoff/(generalMeanRows 1183).c)).2 =
    (291050366417711/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1183).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1183).q*(generalMeanRows 1183).c/2-2 = (207/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable398.value]
  have hcontinuation : (generalMeanRows 1183).q*(generalMeanRows 1183).cutoff/2-2 = (199/65:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable397.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1183).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1183).criticalRate j.val*(generalMeanRows 1183).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1183).c*(generalMeanRows 1183).criticalPoint j.val)).2-
      (generalMeanRows 1183).J/2-(generalMeanRows 1183).error (generalMeanGrid j.val)+
      (generalMeanRows 1183).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1183).c)).2-
      (generalMeanRows 1183).J/2-(generalMeanRows 1183).error 4 := by
  have he : (generalMeanRows 1183).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1183) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1183)
    (generalMeanRows_prefactorDomain 1183) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1183

/-! Kernel-checked entropy margins for general spectral rectangle 1184. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1184
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6525900184) (.branch 2 (.leaf 6337012606) (.leaf 6155561743))) (.branch 5 (.branch 4 (.leaf 5981124000) (.leaf 5813307961)) (.branch 6 (.leaf 5651751412) (.leaf 5496118687)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5346098300) (.leaf 5201400825)) (.branch 10 (.leaf 5061756990) (.leaf 4926915962))) (.branch 13 (.branch 12 (.leaf 4796643806) (.leaf 4670722090)) (.branch 14 (.leaf 4548946626) (.leaf 4431126326))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4317082169) (.branch 17 (.leaf 4206646257) (.leaf 4099660961))) (.branch 20 (.branch 19 (.leaf 3995978141) (.leaf 3895458430)) (.branch 21 (.leaf 3797970592) (.leaf 3703390921)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3611602698) (.leaf 3522495695)) (.branch 25 (.leaf 3435965718) (.leaf 3351914183))) (.branch 28 (.branch 27 (.leaf 3270247733) (.leaf 3190877884)) (.branch 29 (.leaf 3113720696) (.leaf 3038696473)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2965729484) (.branch 32 (.leaf 2894747707) (.leaf 2825682594))) (.branch 35 (.branch 34 (.leaf 2758468850) (.leaf 2693044228)) (.branch 36 (.leaf 2629349347) (.leaf 2567327513)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2506924561) (.leaf 2448088702)) (.branch 40 (.leaf 2390770389) (.leaf 2334922180))) (.branch 43 (.branch 42 (.leaf 2280498628) (.leaf 2227456159)) (.branch 44 (.leaf 2175752975) (.leaf 2125348954))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2076205560) (.branch 47 (.leaf 2028285756) (.leaf 1981553931))) (.branch 50 (.branch 49 (.leaf 1935975821) (.leaf 1891518441)) (.branch 51 (.leaf 1848150022) (.leaf 1805839949)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1764558706) (.leaf 1724277822)) (.branch 55 (.leaf 1684969820) (.leaf 1646608172))) (.branch 58 (.branch 57 (.leaf 1609167253) (.leaf 1572622302)) (.branch 59 (.leaf 1536949383) (.leaf 1502125344))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1468127790) (.branch 62 (.leaf 1434935043) (.leaf 1402526115))) (.branch 65 (.branch 64 (.leaf 1370880680) (.leaf 1339979043)) (.branch 66 (.leaf 1309802118) (.leaf 1280331400)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1251548944) (.leaf 1223437342)) (.branch 70 (.leaf 1195979705) (.leaf 1169159637))) (.branch 73 (.branch 72 (.leaf 1142961222) (.leaf 1117369004)) (.branch 74 (.leaf 1092367970) (.leaf 1067943534))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1044081521) (.branch 77 (.leaf 1020768155) (.leaf 997990042))) (.branch 80 (.branch 79 (.leaf 975734157) (.leaf 953987833)) (.branch 81 (.leaf 932738748) (.leaf 911974914)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 891684665) (.leaf 871856645)) (.branch 85 (.leaf 852479803) (.leaf 833543379))) (.branch 88 (.branch 87 (.leaf 815036894) (.leaf 796950145)) (.branch 89 (.leaf 779273193) (.leaf 761996357)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 745110205) (.branch 92 (.leaf 728605546) (.leaf 712473424))) (.branch 95 (.branch 94 (.leaf 696705111) (.leaf 681292099)) (.branch 96 (.leaf 666226095) (.leaf 651499012)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 637102967) (.leaf 623030273)) (.branch 100 (.leaf 609273434) (.leaf 595825138))) (.branch 103 (.branch 102 (.leaf 582678254) (.leaf 569825826)) (.branch 104 (.leaf 557261068) (.leaf 544977360))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 532968241) (.leaf 521227411)) (.branch 108 (.leaf 509748718) (.leaf 498526161))) (.branch 111 (.branch 110 (.leaf 487553882) (.leaf 476826165)) (.branch 112 (.leaf 466337429) (.leaf 456082228)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 446055245) (.leaf 436251289)) (.branch 116 (.leaf 426665294) (.leaf 417292310))) (.branch 119 (.branch 118 (.leaf 408127509) (.leaf 399166173)) (.branch 120 (.leaf 390403696) (.leaf 381835582)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1184).prefactor = (5932099545452911/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1184).cutoff/(generalMeanRows 1184).c)).2 =
    (567358451098217/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1184).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1184).q*(generalMeanRows 1184).c/2-2 = (87/100:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable246.value]
  have hcontinuation : (generalMeanRows 1184).q*(generalMeanRows 1184).cutoff/2-2 = (199/65:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable397.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1184).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1184).criticalRate j.val*(generalMeanRows 1184).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1184).c*(generalMeanRows 1184).criticalPoint j.val)).2-
      (generalMeanRows 1184).J/2-(generalMeanRows 1184).error (generalMeanGrid j.val)+
      (generalMeanRows 1184).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1184).c)).2-
      (generalMeanRows 1184).J/2-(generalMeanRows 1184).error 4 := by
  have he : (generalMeanRows 1184).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1184) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1184)
    (generalMeanRows_prefactorDomain 1184) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1184

/-! Kernel-checked entropy margins for general spectral rectangle 1185. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1185
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7075381367) (.branch 2 (.leaf 6877979744) (.leaf 6688233571))) (.branch 5 (.branch 4 (.leaf 6505705413) (.leaf 6329991251)) (.branch 6 (.leaf 6160717389) (.leaf 5997537691)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5840131111) (.leaf 5688199489)) (.branch 10 (.leaf 5541465565) (.leaf 5399671197))) (.branch 13 (.branch 12 (.leaf 5262575753) (.leaf 5129954665)) (.branch 14 (.leaf 5001598113) (.leaf 4877309839))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4756906070) (.branch 17 (.leaf 4640214540) (.leaf 4527073598))) (.branch 20 (.branch 19 (.leaf 4417331398) (.leaf 4310845159)) (.branch 21 (.leaf 4207480490) (.leaf 4107110772)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4009616594) (.leaf 3914885233)) (.branch 25 (.leaf 3822810184) (.leaf 3733290718))) (.branch 28 (.branch 27 (.leaf 3646231486) (.leaf 3561542151)) (.branch 29 (.leaf 3479137046) (.leaf 3398934863)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3320858369) (.branch 32 (.leaf 3244834132) (.leaf 3170792283))) (.branch 35 (.branch 34 (.leaf 3098666289) (.leaf 3028392737)) (.branch 36 (.leaf 2959911147) (.leaf 2893163788)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2828095513) (.leaf 2764653603)) (.branch 40 (.leaf 2702787627) (.leaf 2642449303))) (.branch 43 (.branch 42 (.leaf 2583592379) (.leaf 2526172517)) (.branch 44 (.leaf 2470147182) (.leaf 2415475547))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2362118397) (.branch 47 (.leaf 2310038042) (.leaf 2259198238))) (.branch 50 (.branch 49 (.leaf 2209564109) (.leaf 2161102077)) (.branch 51 (.leaf 2113779796) (.leaf 2067566091)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2022430899) (.leaf 1978345212)) (.branch 55 (.leaf 1935281031) (.leaf 1893211316))) (.branch 58 (.branch 57 (.leaf 1852109941) (.leaf 1811951648)) (.branch 59 (.leaf 1772712017) (.leaf 1734367417))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1696894980) (.branch 62 (.leaf 1660272564) (.leaf 1624478720))) (.branch 65 (.branch 64 (.leaf 1589492667) (.leaf 1555294260)) (.branch 66 (.leaf 1521863968) (.leaf 1489182843)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1457232504) (.leaf 1425995109)) (.branch 70 (.leaf 1395453336) (.leaf 1365590363))) (.branch 73 (.branch 72 (.leaf 1336389849) (.leaf 1307835915)) (.branch 74 (.leaf 1279913130) (.leaf 1252606491))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1225901408) (.branch 77 (.leaf 1199783694) (.leaf 1174239544))) (.branch 80 (.branch 79 (.leaf 1149255527) (.leaf 1124818570)) (.branch 81 (.leaf 1100915949) (.leaf 1077535274)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1054664479) (.leaf 1032291815)) (.branch 85 (.leaf 1010405833) (.leaf 988995382))) (.branch 88 (.branch 87 (.leaf 968049592) (.leaf 947557872)) (.branch 89 (.leaf 927509897) (.leaf 907895602)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 888705172) (.branch 92 (.leaf 869929037) (.leaf 851557864))) (.branch 95 (.branch 94 (.leaf 833582549) (.leaf 815994211)) (.branch 96 (.leaf 798784186) (.leaf 781944019)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 765465461) (.leaf 749340461)) (.branch 100 (.leaf 733561161) (.leaf 718119890))) (.branch 103 (.branch 102 (.leaf 703009160) (.leaf 688221662)) (.branch 104 (.leaf 673750257) (.leaf 659587976))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 645728014) (.leaf 632163724)) (.branch 108 (.leaf 618888613) (.leaf 605896342))) (.branch 111 (.branch 110 (.leaf 593180717) (.leaf 580735687)) (.branch 112 (.leaf 568555342) (.leaf 556633906)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 544965738) (.leaf 533545324)) (.branch 116 (.leaf 522367276) (.leaf 511426331))) (.branch 119 (.branch 118 (.leaf 500717342) (.leaf 490235283)) (.branch 120 (.leaf 479975237) (.leaf 469932402)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1185).prefactor = (6165462420171529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1185).cutoff/(generalMeanRows 1185).c)).2 =
    (291050366417711/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1185).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1185).q*(generalMeanRows 1185).c/2-2 = (207/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable398.value]
  have hcontinuation : (generalMeanRows 1185).q*(generalMeanRows 1185).cutoff/2-2 = (199/65:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable397.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1185).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1185).criticalRate j.val*(generalMeanRows 1185).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1185).c*(generalMeanRows 1185).criticalPoint j.val)).2-
      (generalMeanRows 1185).J/2-(generalMeanRows 1185).error (generalMeanGrid j.val)+
      (generalMeanRows 1185).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1185).c)).2-
      (generalMeanRows 1185).J/2-(generalMeanRows 1185).error 4 := by
  have he : (generalMeanRows 1185).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1185) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1185)
    (generalMeanRows_prefactorDomain 1185) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1185

/-! Kernel-checked entropy margins for general spectral rectangle 1186. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1186
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7662420827) (.branch 2 (.leaf 7459324043) (.leaf 7263953622))) (.branch 5 (.branch 4 (.leaf 7075865488) (.leaf 6894649757)) (.branch 6 (.leaf 6719927558) (.leaf 6551348201)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6388586638) (.leaf 6231341206)) (.branch 10 (.leaf 6079331583) (.leaf 5932296966))) (.branch 13 (.branch 12 (.leaf 5789994419) (.leaf 5652197389)) (.branch 14 (.leaf 5518694356) (.leaf 5389287621))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5263792199) (.branch 17 (.leaf 5142034815) (.leaf 5023852993))) (.branch 20 (.branch 19 (.leaf 4909094224) (.leaf 4797615210)) (.branch 21 (.leaf 4689281173) (.leaf 4583965219)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4481547764) (.leaf 4381916002)) (.branch 25 (.leaf 4284963420) (.leaf 4190589353))) (.branch 28 (.branch 27 (.leaf 4098698575) (.leaf 4009200921)) (.branch 29 (.leaf 3922010941) (.leaf 3837047585)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3754233904) (.branch 32 (.leaf 3673496782) (.leaf 3594766687))) (.branch 35 (.branch 34 (.leaf 3517977434) (.leaf 3443065981)) (.branch 36 (.leaf 3369972222) (.leaf 3298638810)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3229010986) (.leaf 3161036419)) (.branch 40 (.leaf 3094665065) (.leaf 3029849029))) (.branch 43 (.branch 42 (.leaf 2966542441) (.leaf 2904701336)) (.branch 44 (.leaf 2844283547) (.leaf 2785248608))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2727557651) (.branch 47 (.leaf 2671173327) (.leaf 2616059718))) (.branch 50 (.branch 49 (.leaf 2562182265) (.leaf 2509507692)) (.branch 51 (.leaf 2458003945) (.leaf 2407640124)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2358386428) (.leaf 2310214101)) (.branch 55 (.leaf 2263095378) (.leaf 2217003439))) (.branch 58 (.branch 57 (.leaf 2171912363) (.leaf 2127797089)) (.branch 59 (.leaf 2084633371) (.leaf 2042397743))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2001067487) (.branch 62 (.leaf 1960620597) (.leaf 1921035745))) (.branch 65 (.branch 64 (.leaf 1882292260) (.leaf 1844370091)) (.branch 66 (.leaf 1807249789) (.leaf 1770912475)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1735339825) (.leaf 1700514039)) (.branch 70 (.leaf 1666417828) (.leaf 1633034389))) (.branch 73 (.branch 72 (.leaf 1600347389) (.leaf 1568340947)) (.branch 74 (.leaf 1536999616) (.leaf 1506308370))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1476252582) (.branch 77 (.leaf 1446818020) (.leaf 1417990824))) (.branch 80 (.branch 79 (.leaf 1389757498) (.leaf 1362104894)) (.branch 81 (.leaf 1335020206) (.leaf 1308490952)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1282504967) (.leaf 1257050392)) (.branch 85 (.leaf 1232115665) (.leaf 1207689509))) (.branch 88 (.branch 87 (.leaf 1183760925) (.leaf 1160319185)) (.branch 89 (.leaf 1137353820) (.leaf 1114854613)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1092811596) (.branch 92 (.leaf 1071215034) (.leaf 1050055427))) (.branch 95 (.branch 94 (.leaf 1029323497) (.leaf 1009010186)) (.branch 96 (.leaf 989106645) (.leaf 969604234)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 950494510) (.leaf 931769225)) (.branch 100 (.leaf 913420322) (.leaf 895439925))) (.branch 103 (.branch 102 (.leaf 877820339) (.leaf 860554043)) (.branch 104 (.leaf 843633685) (.leaf 827052079))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 810802197) (.leaf 794877173)) (.branch 108 (.leaf 779270287) (.leaf 763974974))) (.branch 111 (.branch 110 (.leaf 748984809) (.leaf 734293511)) (.branch 112 (.leaf 719894936) (.leaf 705783074)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 691952047) (.leaf 678396103)) (.branch 116 (.leaf 665109617) (.leaf 652087085))) (.branch 119 (.branch 118 (.leaf 639323119) (.leaf 626812450)) (.branch 120 (.leaf 614549922) (.leaf 602530487)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1186).prefactor = (3154931935136507/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1186).cutoff/(generalMeanRows 1186).c)).2 =
    (60210139954209/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1186).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1186).q*(generalMeanRows 1186).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 1186).q*(generalMeanRows 1186).cutoff/2-2 = (199/65:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable397.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1186).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1186).criticalRate j.val*(generalMeanRows 1186).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1186).c*(generalMeanRows 1186).criticalPoint j.val)).2-
      (generalMeanRows 1186).J/2-(generalMeanRows 1186).error (generalMeanGrid j.val)+
      (generalMeanRows 1186).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1186).c)).2-
      (generalMeanRows 1186).J/2-(generalMeanRows 1186).error 4 := by
  have he : (generalMeanRows 1186).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1186) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1186)
    (generalMeanRows_prefactorDomain 1186) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1186

/-! Kernel-checked entropy margins for general spectral rectangle 1187. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1187
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5997398951) (.branch 2 (.leaf 5823323949) (.leaf 5656054426))) (.branch 5 (.branch 4 (.leaf 5495201762) (.leaf 5340407352)) (.branch 6 (.leaf 5191339777) (.leaf 5047692295)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4909180594) (.leaf 4775540788)) (.branch 10 (.leaf 4646527617) (.leaf 4521912832))) (.branch 13 (.branch 12 (.leaf 4401483740) (.leaf 4285041899)) (.branch 14 (.leaf 4172401931) (.leaf 4063390452))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3957845107) (.branch 17 (.leaf 3855613693) (.leaf 3756553354))) (.branch 20 (.branch 19 (.leaf 3660529867) (.leaf 3567416972)) (.branch 21 (.leaf 3477095777) (.leaf 3389454206)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3304386502) (.leaf 3221792762)) (.branch 25 (.leaf 3141578522) (.leaf 3063654373))) (.branch 28 (.branch 27 (.leaf 2987935607) (.leaf 2914341891)) (.branch 29 (.leaf 2842796974) (.leaf 2773228413)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2705567318) (.branch 32 (.leaf 2639748122) (.leaf 2575708369))) (.branch 35 (.branch 34 (.leaf 2513388513) (.leaf 2452731739)) (.branch 36 (.leaf 2393683793) (.leaf 2336192826)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2280209251) (.leaf 2225685608)) (.branch 40 (.leaf 2172576441) (.leaf 2120838180))) (.branch 43 (.branch 42 (.leaf 2070429042) (.leaf 2021308920)) (.branch 44 (.leaf 1973439301) (.leaf 1926783175))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1881304955) (.branch 47 (.leaf 1836970403) (.leaf 1793746561))) (.branch 50 (.branch 49 (.leaf 1751601685) (.leaf 1710505182)) (.branch 51 (.leaf 1670427559) (.leaf 1631340362)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1593216132) (.leaf 1556028356)) (.branch 55 (.leaf 1519751423) (.leaf 1484360582))) (.branch 58 (.branch 57 (.leaf 1449831905) (.leaf 1416142248)) (.branch 59 (.leaf 1383269220) (.leaf 1351191148))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1319887046) (.branch 62 (.leaf 1289336590) (.leaf 1259520086))) (.branch 65 (.branch 64 (.leaf 1230418448) (.leaf 1202013171)) (.branch 66 (.leaf 1174286311) (.leaf 1147220458)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1120798723) (.leaf 1095004711)) (.branch 70 (.leaf 1069822508) (.leaf 1045236659))) (.branch 73 (.branch 72 (.leaf 1021232153) (.leaf 997794410)) (.branch 74 (.leaf 974909258) (.leaf 952562928))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 930742034) (.branch 77 (.leaf 909433559) (.leaf 888624849))) (.branch 80 (.branch 79 (.leaf 868303592) (.leaf 848457816)) (.branch 81 (.leaf 829075870) (.leaf 810146418)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 791658427) (.leaf 773601158)) (.branch 85 (.leaf 755964157) (.leaf 738737245))) (.branch 88 (.branch 87 (.leaf 721910512) (.leaf 705474306)) (.branch 89 (.leaf 689419226) (.leaf 673736114)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 658416049) (.branch 92 (.leaf 643450341) (.leaf 628830520))) (.branch 95 (.branch 94 (.leaf 614548333) (.leaf 600595738)) (.branch 96 (.leaf 586964895) (.leaf 573648162)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 560638091) (.leaf 547927420)) (.branch 100 (.leaf 535509068) (.leaf 523376133))) (.branch 103 (.branch 102 (.leaf 511521880) (.leaf 499939747)) (.branch 104 (.leaf 488623329) (.leaf 477566383))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 466762817) (.leaf 456206691)) (.branch 108 (.leaf 445892209) (.leaf 435813716))) (.branch 111 (.branch 110 (.leaf 425965696) (.leaf 416342769)) (.branch 112 (.leaf 406939682) (.leaf 397751311)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388772658) (.leaf 379998843)) (.branch 116 (.leaf 371425105) (.leaf 363046797))) (.branch 119 (.branch 118 (.leaf 354859383) (.leaf 346858437)) (.branch 120 (.leaf 339039640) (.leaf 331398773)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1187).prefactor = (557802209426893/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1187).cutoff/(generalMeanRows 1187).c)).2 =
    (605421298251763/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1187).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1187).q*(generalMeanRows 1187).c/2-2 = (1431/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable399.value]
  have hcontinuation : (generalMeanRows 1187).q*(generalMeanRows 1187).cutoff/2-2 = (644/195:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable400.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1187).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1187).criticalRate j.val*(generalMeanRows 1187).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1187).c*(generalMeanRows 1187).criticalPoint j.val)).2-
      (generalMeanRows 1187).J/2-(generalMeanRows 1187).error (generalMeanGrid j.val)+
      (generalMeanRows 1187).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1187).c)).2-
      (generalMeanRows 1187).J/2-(generalMeanRows 1187).error 4 := by
  have he : (generalMeanRows 1187).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1187) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1187)
    (generalMeanRows_prefactorDomain 1187) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1187

/-! Kernel-checked entropy margins for general spectral rectangle 1188. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1188
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6121078386) (.branch 2 (.leaf 5941325763) (.leaf 5768638493))) (.branch 5 (.branch 4 (.leaf 5602613401) (.leaf 5442878389)) (.branch 6 (.leaf 5289089513) (.leaf 5140928384)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4998099845) (.leaf 4860329899)) (.branch 10 (.leaf 4727363843) (.leaf 4598964604))) (.branch 13 (.branch 12 (.leaf 4474911228) (.leaf 4354997528)) (.branch 14 (.leaf 4239030861) (.leaf 4126831021))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4018229236) (.branch 17 (.leaf 3913067259) (.leaf 3811196543))) (.branch 20 (.branch 19 (.leaf 3712477494) (.leaf 3616778781)) (.branch 21 (.leaf 3523976720) (.leaf 3433954702)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3346602676) (.leaf 3261816670)) (.branch 25 (.leaf 3179498364) (.leaf 3099554685))) (.branch 28 (.branch 27 (.leaf 3021897445) (.leaf 2946443005)) (.branch 29 (.leaf 2873111967) (.leaf 2801828891)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2732522032) (.branch 32 (.leaf 2665123104) (.leaf 2599567052))) (.branch 35 (.branch 34 (.leaf 2535791854) (.leaf 2473738327)) (.branch 36 (.leaf 2413349955) (.leaf 2354572728)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2297354987) (.leaf 2241647293)) (.branch 40 (.leaf 2187402291) (.leaf 2134574596))) (.branch 43 (.branch 42 (.leaf 2083120681) (.leaf 2032998769)) (.branch 44 (.leaf 1984168744) (.leaf 1936592056))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1890231643) (.branch 47 (.leaf 1845051847) (.leaf 1801018347))) (.branch 50 (.branch 49 (.leaf 1758098088) (.leaf 1716259219)) (.branch 51 (.leaf 1675471033) (.leaf 1635703911)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1596929274) (.leaf 1559119527)) (.branch 55 (.leaf 1522248020) (.leaf 1486289002))) (.branch 58 (.branch 57 (.leaf 1451217579) (.leaf 1417009679)) (.branch 59 (.leaf 1383642015) (.leaf 1351092052))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1319337971) (.branch 62 (.leaf 1288358646) (.leaf 1258133611))) (.branch 65 (.branch 64 (.leaf 1228643032) (.leaf 1199867685)) (.branch 66 (.leaf 1171788931) (.leaf 1144388692)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1117649431) (.leaf 1091554131)) (.branch 70 (.leaf 1066086273) (.leaf 1041229824))) (.branch 73 (.branch 72 (.leaf 1016969210) (.leaf 993289309)) (.branch 74 (.leaf 970175428) (.leaf 947613292))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 925589027) (.branch 77 (.leaf 904089146) (.leaf 883100539))) (.branch 80 (.branch 79 (.leaf 862610458) (.leaf 842606504)) (.branch 81 (.leaf 823076617) (.leaf 804009066)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 785392436) (.leaf 767215619)) (.branch 85 (.leaf 749467805) (.leaf 732138471))) (.branch 88 (.branch 87 (.leaf 715217374) (.leaf 698694540)) (.branch 89 (.leaf 682560260) (.leaf 666805076)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 651419778) (.branch 92 (.leaf 636395395) (.leaf 621723189))) (.branch 95 (.branch 94 (.leaf 607394647) (.leaf 593401474)) (.branch 96 (.leaf 579735588) (.leaf 566389113)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 553354374) (.leaf 540623890)) (.branch 100 (.leaf 528190371) (.leaf 516046708))) (.branch 103 (.branch 102 (.leaf 504185974) (.leaf 492601413)) (.branch 104 (.leaf 481286440) (.leaf 470234633))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 459439732) (.leaf 448895631)) (.branch 108 (.leaf 438596375) (.leaf 428536158))) (.branch 111 (.branch 110 (.leaf 418709315) (.leaf 409110322)) (.branch 112 (.leaf 399733792) (.leaf 390574468)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381627223) (.leaf 372887054)) (.branch 116 (.leaf 364349083) (.leaf 356008547))) (.branch 119 (.branch 118 (.leaf 347860803) (.leaf 339901316)) (.branch 120 (.leaf 332125666) (.leaf 324529536)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1188).prefactor = (1154623302861379/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1188).cutoff/(generalMeanRows 1188).c)).2 =
    (300340976443933/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1188).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1188).q*(generalMeanRows 1188).c/2-2 = (1453/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable401.value]
  have hcontinuation : (generalMeanRows 1188).q*(generalMeanRows 1188).cutoff/2-2 = (644/195:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable400.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1188).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1188).criticalRate j.val*(generalMeanRows 1188).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1188).c*(generalMeanRows 1188).criticalPoint j.val)).2-
      (generalMeanRows 1188).J/2-(generalMeanRows 1188).error (generalMeanGrid j.val)+
      (generalMeanRows 1188).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1188).c)).2-
      (generalMeanRows 1188).J/2-(generalMeanRows 1188).error 4 := by
  have he : (generalMeanRows 1188).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1188) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1188)
    (generalMeanRows_prefactorDomain 1188) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1188

/-! Kernel-checked entropy margins for general spectral rectangle 1189. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1189
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6606477404) (.branch 2 (.leaf 6419231911) (.leaf 6239229370))) (.branch 5 (.branch 4 (.leaf 6066055461) (.leaf 5899327986)) (.branch 6 (.leaf 5738693846) (.leaf 5583826342)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5434422771) (.leaf 5290202274)) (.branch 10 (.leaf 5150903908) (.leaf 5016284912))) (.branch 13 (.branch 12 (.leaf 4886119152) (.leaf 4760195717)) (.branch 14 (.leaf 4638317648) (.leaf 4520300796))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4405972783) (.branch 17 (.leaf 4295172060) (.leaf 4187747057))) (.branch 20 (.branch 19 (.leaf 4083555400) (.leaf 3982463212)) (.branch 21 (.leaf 3884344462) (.leaf 3789080383)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3696558933) (.leaf 3606674304)) (.branch 25 (.leaf 3519326474) (.leaf 3434420796))) (.branch 28 (.branch 27 (.leaf 3351867622) (.leaf 3271581955)) (.branch 29 (.leaf 3193483131) (.leaf 3117494529)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3043543301) (.branch 32 (.leaf 2971560123) (.leaf 2901478971))) (.branch 35 (.branch 34 (.leaf 2833236904) (.leaf 2766773874)) (.branch 36 (.leaf 2702032547) (.leaf 2638958134)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2577498237) (.leaf 2517602711)) (.branch 40 (.leaf 2459223525) (.leaf 2402314648))) (.branch 43 (.branch 42 (.leaf 2346831927) (.leaf 2292732987)) (.branch 44 (.leaf 2239977131) (.leaf 2188525246))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2138339723) (.branch 47 (.leaf 2089384374) (.leaf 2041624358))) (.branch 50 (.branch 49 (.leaf 1995026113) (.leaf 1949557292)) (.branch 51 (.leaf 1905186700) (.leaf 1861884242)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1819620865) (.leaf 1778368510)) (.branch 55 (.leaf 1738100070) (.leaf 1698789340))) (.branch 58 (.branch 57 (.leaf 1660410978) (.leaf 1622940469)) (.branch 59 (.leaf 1586354085) (.leaf 1550628855))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1515742529) (.branch 62 (.leaf 1481673549) (.leaf 1448401020))) (.branch 65 (.branch 64 (.leaf 1415904686) (.leaf 1384164900)) (.branch 66 (.leaf 1353162600) (.leaf 1322879291)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1293297019) (.leaf 1264398351)) (.branch 70 (.leaf 1236166356) (.leaf 1208584586))) (.branch 73 (.branch 72 (.leaf 1181637060) (.leaf 1155308246)) (.branch 74 (.leaf 1129583044) (.leaf 1104446772))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1079885153) (.branch 77 (.leaf 1055884297) (.leaf 1032430693))) (.branch 80 (.branch 79 (.leaf 1009511194) (.leaf 987113001)) (.branch 81 (.leaf 965223661) (.leaf 943831046)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 922923348) (.leaf 902489069)) (.branch 85 (.leaf 882517009) (.leaf 862996257))) (.branch 88 (.branch 87 (.leaf 843916186) (.leaf 825266438)) (.branch 89 (.leaf 807036920) (.leaf 789217797)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 771799481) (.branch 92 (.leaf 754772626) (.leaf 738128121))) (.branch 95 (.branch 94 (.leaf 721857080) (.leaf 705950841)) (.branch 96 (.leaf 690400956) (.leaf 675199185)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 660337491) (.leaf 645808035)) (.branch 100 (.leaf 631603170) (.leaf 617715433))) (.branch 103 (.branch 102 (.leaf 604137546) (.leaf 590862404)) (.branch 104 (.leaf 577883077) (.leaf 565192799))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 552784969) (.leaf 540653143)) (.branch 108 (.leaf 528791033) (.leaf 517192498))) (.branch 111 (.branch 110 (.leaf 505851546) (.leaf 494762326)) (.branch 112 (.leaf 483919127) (.leaf 473316371)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 462948613) (.leaf 452810537)) (.branch 116 (.leaf 442896951) (.leaf 433202785))) (.branch 119 (.branch 118 (.leaf 423723087) (.leaf 414453023)) (.branch 120 (.leaf 405387870) (.leaf 396523015)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1189).prefactor = (5975034470015151/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1189).cutoff/(generalMeanRows 1189).c)).2 =
    (307483955067671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1189).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1189).q*(generalMeanRows 1189).cutoff/2-2 = (644/195:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable400.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1189).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1189).criticalRate j.val*(generalMeanRows 1189).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1189).c*(generalMeanRows 1189).criticalPoint j.val)).2-
      (generalMeanRows 1189).J/2-(generalMeanRows 1189).error (generalMeanGrid j.val)+
      (generalMeanRows 1189).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1189).c)).2-
      (generalMeanRows 1189).J/2-(generalMeanRows 1189).error 4 := by
  have he : (generalMeanRows 1189).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1189) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1189)
    (generalMeanRows_prefactorDomain 1189) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1189

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock16 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 16 i) := by
  fin_cases i
  · exact EntropyRow1120.numerical
  · exact EntropyRow1121.numerical
  · exact EntropyRow1122.numerical
  · exact EntropyRow1123.numerical
  · exact EntropyRow1124.numerical
  · exact EntropyRow1125.numerical
  · exact EntropyRow1126.numerical
  · exact EntropyRow1127.numerical
  · exact EntropyRow1128.numerical
  · exact EntropyRow1129.numerical
  · exact EntropyRow1130.numerical
  · exact EntropyRow1131.numerical
  · exact EntropyRow1132.numerical
  · exact EntropyRow1133.numerical
  · exact EntropyRow1134.numerical
  · exact EntropyRow1135.numerical
  · exact EntropyRow1136.numerical
  · exact EntropyRow1137.numerical
  · exact EntropyRow1138.numerical
  · exact EntropyRow1139.numerical
  · exact EntropyRow1140.numerical
  · exact EntropyRow1141.numerical
  · exact EntropyRow1142.numerical
  · exact EntropyRow1143.numerical
  · exact EntropyRow1144.numerical
  · exact EntropyRow1145.numerical
  · exact EntropyRow1146.numerical
  · exact EntropyRow1147.numerical
  · exact EntropyRow1148.numerical
  · exact EntropyRow1149.numerical
  · exact EntropyRow1150.numerical
  · exact EntropyRow1151.numerical
  · exact EntropyRow1152.numerical
  · exact EntropyRow1153.numerical
  · exact EntropyRow1154.numerical
  · exact EntropyRow1155.numerical
  · exact EntropyRow1156.numerical
  · exact EntropyRow1157.numerical
  · exact EntropyRow1158.numerical
  · exact EntropyRow1159.numerical
  · exact EntropyRow1160.numerical
  · exact EntropyRow1161.numerical
  · exact EntropyRow1162.numerical
  · exact EntropyRow1163.numerical
  · exact EntropyRow1164.numerical
  · exact EntropyRow1165.numerical
  · exact EntropyRow1166.numerical
  · exact EntropyRow1167.numerical
  · exact EntropyRow1168.numerical
  · exact EntropyRow1169.numerical
  · exact EntropyRow1170.numerical
  · exact EntropyRow1171.numerical
  · exact EntropyRow1172.numerical
  · exact EntropyRow1173.numerical
  · exact EntropyRow1174.numerical
  · exact EntropyRow1175.numerical
  · exact EntropyRow1176.numerical
  · exact EntropyRow1177.numerical
  · exact EntropyRow1178.numerical
  · exact EntropyRow1179.numerical
  · exact EntropyRow1180.numerical
  · exact EntropyRow1181.numerical
  · exact EntropyRow1182.numerical
  · exact EntropyRow1183.numerical
  · exact EntropyRow1184.numerical
  · exact EntropyRow1185.numerical
  · exact EntropyRow1186.numerical
  · exact EntropyRow1187.numerical
  · exact EntropyRow1188.numerical
  · exact EntropyRow1189.numerical
end SingularValueBounds.KL.Certificates
